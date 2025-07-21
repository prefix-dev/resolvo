use std::{
    fs::File,
    io::BufReader,
    ops::Add,
    time::{Duration, Instant, SystemTime},
};

use clap::Parser;
use console::style;
use csv::WriterBuilder;
use itertools::Itertools;
use rand::{
    Rng, SeedableRng,
    distr::{Distribution, weighted::WeightedIndex},
    prelude::IteratorRandom,
    rngs::StdRng,
};
use resolvo::{Problem, Requirement, Solver, UnsolvableOrCancelled, snapshot::DependencySnapshot};

#[derive(Parser)]
#[clap(version = "0.1.0", author = "Bas Zalmstra <zalmstra.bas@gmail.com>")]
struct Opts {
    snapshot: String,

    /// The maximum number of requirements to solve
    #[clap(long, short = 'n', default_value = "1000")]
    limit: usize,

    /// The timeout to use for solving requirements in seconds. If a solve takes
    /// longer if will be cancelled.
    #[clap(long, default_value = "60")]
    timeout: u64,

    /// The random seed to use for generating the requirements.
    #[clap(long, default_value = "0")]
    seed: u64,
}

#[derive(Debug, serde::Serialize)]
struct Record {
    package: String,
    duration: f64,
    error: Option<String>,
    records: Option<usize>,
}

fn main() {
    let opts: Opts = Opts::parse();

    eprintln!("Loading snapshot ...");
    let snapshot_file = BufReader::new(File::open(opts.snapshot).unwrap());
    let snapshot: DependencySnapshot = serde_json::from_reader(snapshot_file).unwrap();

    let mut writer = WriterBuilder::new()
        .has_headers(true)
        .from_path("timings.csv")
        .unwrap();

    // Generate a range of problems.
    let mut rng = StdRng::seed_from_u64(0);
    let requirement_dist = WeightedIndex::new([
        10, // 10 times more likely to pick a package
        if !snapshot.version_sets.is_empty() {
            1
        } else {
            0
        },
        if !snapshot.version_set_unions.is_empty() {
            1
        } else {
            0
        },
    ])
    .unwrap();
    for i in 0..opts.limit {
        // Construct a fresh provider from the snapshot
        let mut provider = snapshot
            .provider()
            .with_timeout(SystemTime::now().add(Duration::from_secs(opts.timeout)));

        // Construct a problem with a random number of requirements.
        let mut requirements: Vec<Requirement> = Vec::new();

        // Determine the number of requirements to solve for.
        let num_requirements = rng.random_range(1..=10usize);
        for _ in 0..num_requirements {
            match requirement_dist.sample(&mut rng) {
                0 => {
                    // Add a package requirement
                    let (package, _) = snapshot.packages.iter().choose(&mut rng).unwrap();
                    let package_requirement = provider.add_package_requirement(package, "*");
                    requirements.push(package_requirement.into());
                }
                1 => {
                    // Add a version set requirement
                    let (version_set_id, _) =
                        snapshot.version_sets.iter().choose(&mut rng).unwrap();
                    requirements.push(version_set_id.into());
                }
                2 => {
                    // Add a version set union requirement
                    let (version_set_union_id, _) =
                        snapshot.version_set_unions.iter().choose(&mut rng).unwrap();
                    requirements.push(version_set_union_id.into());
                }
                _ => unreachable!(),
            }
        }

        eprintln!(
            "solving ({}/{})...\n{}",
            i + 1,
            opts.limit,
            requirements.iter().format_with("\n", |requirement, f| {
                f(&format_args!(
                    "- {}",
                    style(requirement.display(&provider)).dim()
                ))
            })
        );

        let problem_name = requirements
            .iter()
            .format_with("\n", |requirement, f| {
                f(&format_args!("{}", requirement.display(&provider)))
            })
            .to_string();

        let start = Instant::now();

        let problem = Problem::default().requirements(requirements);
        let mut solver = Solver::new(provider);
        let mut records = None;
        let mut error = None;
        let result = solver.solve(problem);
        let duration = start.elapsed();
        match result {
            Ok(solution) => {
                eprintln!(
                    "{}",
                    style(format!(
                        "==> OK in {:.2}ms, {} records",
                        duration.as_secs_f64() * 1000.0,
                        solution.len(),
                    ))
                    .green()
                );
                records = Some(solution.len())
            }
            Err(UnsolvableOrCancelled::Unsolvable(problem)) => {
                eprintln!(
                    "{}",
                    style(format!(
                        "==> FAIL in {:.2}ms",
                        duration.as_secs_f64() * 1000.0
                    ))
                    .yellow()
                );
                error = Some(problem.display_user_friendly(&solver).to_string());
            }
            Err(_) => {
                eprintln!(
                    "{}",
                    style(format!(
                        "==> CANCELLED after {:.2}ms",
                        duration.as_secs_f64() * 1000.0
                    ))
                    .red()
                );
            }
        }

        writer
            .serialize(Record {
                package: problem_name,
                duration: duration.as_secs_f64(),
                error,
                records,
            })
            .unwrap();

        if i % 10 == 0 {
            writer.flush().unwrap();
        }
    }

    writer.flush().unwrap();
}
