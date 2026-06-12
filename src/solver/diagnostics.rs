use std::io::Write;

use ahash::HashMap;
use itertools::Itertools;

use crate::{
    DependencyProvider, Solver,
    runtime::AsyncRuntime,
    solver::clause::{Clause, WatchedLiterals},
};

impl<D: DependencyProvider, RT: AsyncRuntime> Solver<D, RT> {
    /// Reports diagnostics about the current state of the solver.
    pub(crate) fn report_diagnostics(&self) {
        let mut forbid_clauses_by_name = HashMap::default();
        let mut forbid_clauses = 0usize;
        let mut requires_clauses = 0usize;
        let mut locked_clauses = 0usize;
        let mut learned_clauses = 0usize;
        let mut constrains_clauses = 0usize;
        let mut any_of_clauses = 0usize;
        let mut excluded_clauses = 0usize;
        let clauses = &self.state.clauses.kinds;

        // Count binary vs non-binary watched clauses
        let mut binary_watched = 0usize;
        let mut long_watched = 0usize;
        let mut assertion_clauses = 0usize;

        for (i, clause) in clauses.iter().enumerate() {
            match clause {
                Clause::ForbidMultipleInstances(_a, _b, name_id) => {
                    let count = forbid_clauses_by_name.entry(name_id).or_insert(0usize);
                    *count += 1;
                    forbid_clauses += 1;
                }
                Clause::Requires(..) => {
                    requires_clauses += 1;
                }
                Clause::Lock(..) => {
                    locked_clauses += 1;
                }
                Clause::Learnt(..) => {
                    learned_clauses += 1;
                }
                Clause::Constrains(..)
                | Clause::ConstrainsExcluded(..)
                | Clause::ConstrainsParent(..) => {
                    constrains_clauses += 1;
                }
                Clause::AnyOf(..) => {
                    any_of_clauses += 1;
                }
                Clause::Excluded(..) => {
                    excluded_clauses += 1;
                }
                _ => {}
            }

            // Classify by watch structure
            match &self.state.clauses.watched_literals[i] {
                None => assertion_clauses += 1,
                Some(_) => match clause {
                    Clause::Constrains(..)
                    | Clause::ConstrainsExcluded(..)
                    | Clause::ConstrainsParent(..)
                    | Clause::ForbidMultipleInstances(..)
                    | Clause::Lock(..)
                    | Clause::AnyOf(..) => binary_watched += 1,
                    _ => long_watched += 1,
                },
            }
        }

        let mut writer = tabwriter::TabWriter::new(Vec::new());
        writeln!(
            writer,
            "Total number of solvables:\t{}",
            self.state.decision_tracker.len()
        )
        .unwrap();
        writeln!(
            writer,
            "Total number of watches:\t{} ({})",
            self.state.watches.len(),
            human_bytes::human_bytes(self.state.watches.size_in_bytes() as f64)
        )
        .unwrap();
        writeln!(
            writer,
            "Total number of variables:\t{} ({})",
            self.state.variable_map.count(),
            human_bytes::human_bytes(self.state.variable_map.size_in_bytes() as f64)
        )
        .unwrap();
        writeln!(
            writer,
            "Total number of clauses:\t{} ({})",
            clauses.len(),
            human_bytes::human_bytes(
                (clauses.len()
                    * (std::mem::size_of::<Clause<D::NameId>>()
                        + std::mem::size_of::<WatchedLiterals>())) as f64
            )
        )
        .unwrap();
        writeln!(writer, "- Requires:\t{}", requires_clauses).unwrap();
        writeln!(writer, "- Constrains:\t{}", constrains_clauses).unwrap();
        writeln!(writer, "- Lock:\t{}", locked_clauses).unwrap();
        writeln!(writer, "- Learned:\t{}", learned_clauses).unwrap();
        writeln!(writer, "- ForbidMultiple:\t{}", forbid_clauses).unwrap();
        writeln!(writer, "- AnyOf:\t{}", any_of_clauses).unwrap();
        writeln!(writer, "- Excluded:\t{}", excluded_clauses).unwrap();

        writeln!(writer, "\nClause structure:").unwrap();
        writeln!(
            writer,
            "- Binary (2-literal, immovable watches):\t{}\t({:.1}%)",
            binary_watched,
            100.0 * binary_watched as f64 / clauses.len().max(1) as f64
        )
        .unwrap();
        writeln!(
            writer,
            "- Long (movable watches):\t{}\t({:.1}%)",
            long_watched,
            100.0 * long_watched as f64 / clauses.len().max(1) as f64
        )
        .unwrap();
        writeln!(
            writer,
            "- Assertions (no watches):\t{}\t({:.1}%)",
            assertion_clauses,
            100.0 * assertion_clauses as f64 / clauses.len().max(1) as f64
        )
        .unwrap();

        for (name_id, count) in forbid_clauses_by_name
            .iter()
            .sorted_by_key(|(_, count)| **count)
            .rev()
            .take(5)
        {
            writeln!(
                writer,
                "  - {}:\t{}",
                self.provider().display_name(**name_id),
                count
            )
            .unwrap();
        }

        if forbid_clauses_by_name.len() > 5 {
            writeln!(writer, "  ...").unwrap();
        }

        // Propagation counters
        let counters = &self.state.propagation_counters;
        writeln!(writer, "\n=== Propagation Statistics ===").unwrap();
        writeln!(writer, "propagate() calls:\t{}", counters.propagate_calls).unwrap();
        writeln!(
            writer,
            "Decisions propagated:\t{}",
            counters.decisions_propagated
        )
        .unwrap();
        writeln!(writer, "Total clause visits:\t{}", counters.clause_visits).unwrap();
        let total = counters.clause_visits.max(1) as f64;
        writeln!(
            writer,
            "- Early skips (other watch true):\t{}\t({:.1}%)",
            counters.early_skips,
            100.0 * counters.early_skips as f64 / total
        )
        .unwrap();
        writeln!(
            writer,
            "- Watch moves (found new literal):\t{}\t({:.1}%)",
            counters.watch_moves,
            100.0 * counters.watch_moves as f64 / total
        )
        .unwrap();
        writeln!(
            writer,
            "- Unit propagations:\t{}\t({:.1}%)",
            counters.unit_propagations,
            100.0 * counters.unit_propagations as f64 / total
        )
        .unwrap();
        writeln!(writer, "Conflicts:\t{}", counters.conflicts).unwrap();

        writeln!(writer, "\nClause visits by type:").unwrap();
        let vbt = &counters.visits_by_type;
        writeln!(writer, "- Requires:\t{}", vbt.requires).unwrap();
        writeln!(writer, "- Constrains:\t{}", vbt.constrains).unwrap();
        writeln!(writer, "- ForbidMultiple:\t{}", vbt.forbid_multiple).unwrap();
        writeln!(writer, "- Lock:\t{}", vbt.lock).unwrap();
        writeln!(writer, "- Learnt:\t{}", vbt.learnt).unwrap();
        writeln!(writer, "- AnyOf:\t{}", vbt.any_of).unwrap();

        writeln!(writer, "\nnext_unwatched_literal calls by type:").unwrap();
        let uwt = &counters.unwatched_calls_by_type;
        writeln!(writer, "- Requires:\t{}", uwt.requires).unwrap();
        writeln!(writer, "- Constrains:\t{}", uwt.constrains).unwrap();
        writeln!(writer, "- ForbidMultiple:\t{}", uwt.forbid_multiple).unwrap();
        writeln!(writer, "- Lock:\t{}", uwt.lock).unwrap();
        writeln!(writer, "- Learnt:\t{}", uwt.learnt).unwrap();
        writeln!(writer, "- AnyOf:\t{}", uwt.any_of).unwrap();

        if counters.clause_visits > 0 {
            writeln!(
                writer,
                "\nAvg clause visits per decision:\t{:.1}",
                counters.clause_visits as f64 / counters.decisions_propagated.max(1) as f64
            )
            .unwrap();
        }

        let queue_counters = &self.state.decide_queue.counters;
        writeln!(writer, "\n=== Decide Queue ===").unwrap();
        writeln!(writer, "Sync touches:\t{}", queue_counters.sync_touches).unwrap();
        writeln!(
            writer,
            "Selection visits:\t{}",
            queue_counters.selection_visits
        )
        .unwrap();
        writeln!(writer, "- Hot:\t{}", queue_counters.hot_visits).unwrap();
        writeln!(writer, "Dequeues:\t{}", queue_counters.dequeues).unwrap();
        writeln!(writer, "Walk evaluations:\t{}", queue_counters.walk_evals).unwrap();

        writeln!(writer, "\n=== Phase Timing ===").unwrap();
        writeln!(
            writer,
            "Encoding (DP -> clauses):\t{:.2}ms",
            counters.encoding_duration.as_secs_f64() * 1000.0
        )
        .unwrap();
        writeln!(
            writer,
            "Propagation:\t{:.2}ms",
            counters.propagation_duration.as_secs_f64() * 1000.0
        )
        .unwrap();
        writeln!(
            writer,
            "Decision (choose next var):\t{:.2}ms",
            counters.decide_duration.as_secs_f64() * 1000.0
        )
        .unwrap();
        writeln!(
            writer,
            "Learning (conflict analysis):\t{:.2}ms",
            counters.learn_duration.as_secs_f64() * 1000.0
        )
        .unwrap();

        let report = String::from_utf8(writer.into_inner().unwrap()).unwrap();

        tracing::info!("Solver diagnostics:\n{}", report);
    }
}
