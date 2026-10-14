//! Types to examine why a problem was unsatisfiable, and to report the causes
//! to the user.

use std::{collections::HashSet, fmt, fmt::Formatter, hash::Hash, rc::Rc};

use ahash::HashMap;
use itertools::Itertools;
use petgraph::{
    Direction,
    graph::{DiGraph, EdgeIndex, EdgeReference, NodeIndex},
    visit::{Bfs, DfsPostOrder, EdgeRef},
};

use crate::{
    DenseIndex, DependencyProvider, Interner, Requirement, SolvableId, SolverId, StringId,
    VariableId, VersionSetId,
    internal::{id::ClauseId, solver_id::SolvableIdOrRoot},
    runtime::AsyncRuntime,
    solver::{Solver, clause::Clause, variable_map::VariableOrigin},
};

/// Represents the cause of the solver being unable to find a solution
#[derive(Debug)]
pub struct Conflict {
    /// The clauses involved in an unsatisfiable conflict
    clauses: Vec<ClauseId>,
}

impl Conflict {
    pub(crate) fn default() -> Self {
        Self {
            clauses: Vec::new(),
        }
    }

    pub(crate) fn add_clause(&mut self, clause_id: ClauseId) {
        if !self.clauses.contains(&clause_id) {
            self.clauses.push(clause_id);
        }
    }

    /// Generates a graph representation of the conflict (see [`ConflictGraph`]
    /// for details)
    pub fn graph<D: DependencyProvider, RT: AsyncRuntime>(
        &self,
        solver: &Solver<D, RT>,
    ) -> ConflictGraph<D::SolvableId> {
        let state = &solver.state;

        let mut graph =
            DiGraph::<ConflictNode<D::SolvableId>, ConflictEdge<D::SolvableId>>::default();
        let mut nodes: HashMap<SolvableIdOrRoot<D::SolvableId>, NodeIndex> = HashMap::default();
        let mut excluded_nodes: HashMap<StringId, NodeIndex> = HashMap::default();

        let root_node = Self::add_node(&mut graph, &mut nodes, SolvableIdOrRoot::root());
        let unresolved_node = graph.add_node(ConflictNode::UnresolvedDependency);
        let mut last_node_by_name: HashMap<D::NameId, NodeIndex> = HashMap::default();

        // The shared constrains encoding splits each (parent, excluded
        // candidate) pair over two clauses linked by an auxiliary variable.
        // Collect both sides per auxiliary variable so the original
        // `parent -> candidate` edges can be reconstructed in the loop below.
        let mut constrains_aux_parents: HashMap<VariableId, Vec<SolvableIdOrRoot<D::SolvableId>>> =
            HashMap::default();
        let mut constrains_aux_candidates: HashMap<
            VariableId,
            Vec<SolvableIdOrRoot<D::SolvableId>>,
        > = HashMap::default();
        for clause_id in &self.clauses {
            match state.clauses.kinds[clause_id.to_index()] {
                Clause::ConstrainsParent(parent, aux, _) => {
                    let parent = parent
                        .as_solvable_or_root(&state.variable_map)
                        .expect("constrains parents are solvables or root");
                    constrains_aux_parents.entry(aux).or_default().push(parent);
                }
                Clause::ConstrainsExcluded(candidate, aux, _) => {
                    let candidate = candidate
                        .as_solvable_or_root(&state.variable_map)
                        .expect("excluded candidates are solvables");
                    constrains_aux_candidates
                        .entry(aux)
                        .or_default()
                        .push(candidate);
                }
                _ => {}
            }
        }

        // If only one side of a chain is part of the conflict, recover the
        // other side from the assignment reason of the auxiliary variable.
        let reason_clause = |aux: VariableId| {
            state
                .decision_tracker
                .find_clause_for_assignment(aux)
                .map(|clause_id| state.clauses.kinds[clause_id.to_index()])
        };
        for &aux in constrains_aux_parents.keys() {
            if constrains_aux_candidates.contains_key(&aux) {
                continue;
            }
            if let Some(Clause::ConstrainsExcluded(candidate, _, _)) = reason_clause(aux) {
                let candidate = candidate
                    .as_solvable_or_root(&state.variable_map)
                    .expect("excluded candidates are solvables");
                constrains_aux_candidates.insert(aux, vec![candidate]);
            }
        }
        for &aux in constrains_aux_candidates.keys() {
            if constrains_aux_parents.contains_key(&aux) {
                continue;
            }
            if let Some(Clause::ConstrainsParent(parent, _, _)) = reason_clause(aux) {
                let parent = parent
                    .as_solvable_or_root(&state.variable_map)
                    .expect("constrains parents are solvables or root");
                constrains_aux_parents.insert(aux, vec![parent]);
            }
        }

        // The shared requires encoding links a requirer to its candidate
        // disjunction through a gate variable: a binary `AnyOf(gate, parent)`
        // clause per requirer plus one `Requires(gate, ..)` disjunction. Collect
        // the requirers per gate so the original `parent -> candidate` edges can
        // be reconstructed when the gate's `Requires` clause is processed below.
        let mut requires_gate_parents: HashMap<VariableId, Vec<SolvableIdOrRoot<D::SolvableId>>> =
            HashMap::default();
        for clause_id in &self.clauses {
            if let Clause::AnyOf(selected, parent) = state.clauses.kinds[clause_id.to_index()] {
                if matches!(
                    state.variable_map.origin(selected),
                    VariableOrigin::RequiresGate(_)
                ) {
                    if let Some(parent) = parent.as_solvable_or_root(&state.variable_map) {
                        requires_gate_parents
                            .entry(selected)
                            .or_default()
                            .push(parent);
                    }
                }
            }
        }
        // If a gate is part of the conflict but its requirer's implication
        // clause is not, recover the requirer from the gate's assignment reason.
        for clause_id in &self.clauses {
            if let Clause::Requires(gate, _, _) = state.clauses.kinds[clause_id.to_index()] {
                if matches!(
                    state.variable_map.origin(gate),
                    VariableOrigin::RequiresGate(_)
                ) && !requires_gate_parents.contains_key(&gate)
                {
                    if let Some(Clause::AnyOf(_, parent)) = reason_clause(gate) {
                        if let Some(parent) = parent.as_solvable_or_root(&state.variable_map) {
                            requires_gate_parents.insert(gate, vec![parent]);
                        }
                    }
                }
            }
        }

        // Avoids adding the same edge once for each side of a chain.
        type ConstrainsEdge<S> = (SolvableIdOrRoot<S>, SolvableIdOrRoot<S>, VersionSetId);
        let mut constrains_edges: HashSet<ConstrainsEdge<D::SolvableId>> = HashSet::new();

        for clause_id in &self.clauses {
            let clause = &state.clauses.kinds[clause_id.to_index()];
            match clause {
                Clause::InstallRoot => (),
                Clause::Excluded(solvable, reason) => {
                    tracing::trace!("{solvable:?} is excluded");
                    let solvable = solvable
                        .as_solvable(&state.variable_map)
                        .expect("only solvables can be excluded");

                    let package_node = Self::add_node(&mut graph, &mut nodes, solvable.into());
                    let excluded_node = excluded_nodes
                        .entry(*reason)
                        .or_insert_with(|| graph.add_node(ConflictNode::Excluded(*reason)));

                    graph.add_edge(
                        package_node,
                        *excluded_node,
                        ConflictEdge::Conflict(ConflictCause::Excluded),
                    );
                }
                Clause::Learnt(..) => unreachable!(),
                &Clause::Requires(package_id, _condition, version_set_id) => {
                    // The requiring solvable(s). With the shared requires
                    // encoding the clause's parent is a gate variable; expand it
                    // to the real requirers reconstructed above. A direct
                    // requires clause has a single solvable/root parent.
                    let parents: Vec<SolvableIdOrRoot<D::SolvableId>> =
                        match package_id.as_solvable_or_root(&state.variable_map) {
                            Some(solvable) => vec![solvable],
                            None => requires_gate_parents
                                .get(&package_id)
                                .cloned()
                                .unwrap_or_default(),
                        };

                    let candidates = solver.async_runtime.block_on(solver.cache.get_or_cache_sorted_candidates(version_set_id)).unwrap_or_else(|_| {
                        unreachable!("The version set was used in the solver, so it must have been cached. Therefore cancellation is impossible here and we cannot get an `Err(...)`")
                    });

                    for parent in parents {
                        let package_node = Self::add_node(&mut graph, &mut nodes, parent);
                        if candidates.is_empty() {
                            tracing::trace!(
                                "{parent:?} requires {version_set_id:?}, which has no candidates"
                            );
                            graph.add_edge(
                                package_node,
                                unresolved_node,
                                ConflictEdge::Requires(version_set_id),
                            );
                        } else {
                            for &candidate_id in candidates {
                                tracing::trace!("{parent:?} requires {candidate_id:?}");

                                let candidate_node =
                                    Self::add_node(&mut graph, &mut nodes, candidate_id.into());
                                graph.add_edge(
                                    package_node,
                                    candidate_node,
                                    ConflictEdge::Requires(version_set_id),
                                );
                            }
                        }
                    }
                }
                &Clause::Lock(locked, forbidden) => {
                    let locked_solvable = locked
                        .as_solvable(&state.variable_map)
                        .expect("only solvables can be excluded");
                    let forbidden_solvable = forbidden
                        .as_solvable(&state.variable_map)
                        .expect("only solvables can be excluded");
                    let node2_id =
                        Self::add_node(&mut graph, &mut nodes, forbidden_solvable.into());
                    let conflict = ConflictCause::Locked(locked_solvable);
                    graph.add_edge(root_node, node2_id, ConflictEdge::Conflict(conflict));
                }
                &Clause::ForbidMultipleInstances(instance1_id, instance2_id, _) => {
                    let solvable1 = instance1_id
                        .as_solvable_or_root(&state.variable_map)
                        .expect("only solvables can be excluded");
                    let node1_id = Self::add_node(&mut graph, &mut nodes, solvable1);

                    let VariableOrigin::ForbidMultiple(name) =
                        state.variable_map.origin(instance2_id.variable())
                    else {
                        unreachable!("expected only forbid variables")
                    };

                    let previous_node = last_node_by_name.insert(name, node1_id);
                    if let Some(previous_node) = previous_node {
                        graph.add_edge(
                            previous_node,
                            node1_id,
                            ConflictEdge::Conflict(ConflictCause::ForbidMultipleInstances),
                        );
                    }
                }
                &Clause::Constrains(package_id, dep_id, version_set_id) => {
                    let package_solvable = package_id
                        .as_solvable_or_root(&state.variable_map)
                        .expect("only solvables can be excluded");
                    let dependency_solvable = dep_id
                        .as_solvable_or_root(&state.variable_map)
                        .expect("only solvables can be excluded");

                    let package_node = Self::add_node(&mut graph, &mut nodes, package_solvable);
                    let dep_node = Self::add_node(&mut graph, &mut nodes, dependency_solvable);

                    graph.add_edge(
                        package_node,
                        dep_node,
                        ConflictEdge::Conflict(ConflictCause::Constrains(version_set_id)),
                    );
                }
                &Clause::ConstrainsParent(package_id, aux, version_set_id) => {
                    let package_solvable = package_id
                        .as_solvable_or_root(&state.variable_map)
                        .expect("constrains parents are solvables or root");

                    let Some(candidates) = constrains_aux_candidates.get(&aux) else {
                        continue;
                    };

                    for &dependency_solvable in candidates {
                        if !constrains_edges.insert((
                            package_solvable,
                            dependency_solvable,
                            version_set_id,
                        )) {
                            continue;
                        }

                        let package_node = Self::add_node(&mut graph, &mut nodes, package_solvable);
                        let dep_node = Self::add_node(&mut graph, &mut nodes, dependency_solvable);

                        graph.add_edge(
                            package_node,
                            dep_node,
                            ConflictEdge::Conflict(ConflictCause::Constrains(version_set_id)),
                        );
                    }
                }
                &Clause::ConstrainsExcluded(dep_id, aux, version_set_id) => {
                    let dependency_solvable = dep_id
                        .as_solvable_or_root(&state.variable_map)
                        .expect("excluded candidates are solvables");

                    let Some(parents) = constrains_aux_parents.get(&aux) else {
                        continue;
                    };

                    for &package_solvable in parents {
                        if !constrains_edges.insert((
                            package_solvable,
                            dependency_solvable,
                            version_set_id,
                        )) {
                            continue;
                        }

                        let package_node = Self::add_node(&mut graph, &mut nodes, package_solvable);
                        let dep_node = Self::add_node(&mut graph, &mut nodes, dependency_solvable);

                        graph.add_edge(
                            package_node,
                            dep_node,
                            ConflictEdge::Conflict(ConflictCause::Constrains(version_set_id)),
                        );
                    }
                }
                Clause::AnyOf(selected, _variable) => {
                    // No edge: at-least-one `AnyOf` clauses can never be false
                    // (the selected variable is only ever propagated true), and
                    // requires-gate implications are represented by the
                    // `parent -> candidate` edges drawn from the gate's
                    // `Requires` clause above.
                    if !matches!(
                        state.variable_map.origin(*selected),
                        VariableOrigin::RequiresGate(_)
                    ) {
                        let decision_map = solver.state.decision_tracker.map();
                        debug_assert_ne!(selected.positive().eval(decision_map), Some(false));
                    }
                }
            }
        }

        let unresolved_node = if graph
            .edges_directed(unresolved_node, Direction::Incoming)
            .next()
            .is_none()
        {
            graph.remove_node(unresolved_node);
            None
        } else {
            Some(unresolved_node)
        };

        // Sanity check: all nodes are reachable from root
        let mut visited_nodes = HashSet::new();
        let mut bfs = Bfs::new(&graph, root_node);
        while let Some(nx) = bfs.next(&graph) {
            visited_nodes.insert(nx);
        }
        assert_eq!(graph.node_count(), visited_nodes.len());

        ConflictGraph {
            graph,
            root_node,
            unresolved_node,
        }
    }

    fn add_node<S: SolverId>(
        graph: &mut DiGraph<ConflictNode<S>, ConflictEdge<S>>,
        nodes: &mut HashMap<SolvableIdOrRoot<S>, NodeIndex>,
        solvable_id: SolvableIdOrRoot<S>,
    ) -> NodeIndex {
        *nodes
            .entry(solvable_id)
            .or_insert_with(|| graph.add_node(ConflictNode::from_solvable_or_root(solvable_id)))
    }

    /// Display a user-friendly error explaining the conflict
    pub fn display_user_friendly<'a, D: DependencyProvider, RT: AsyncRuntime>(
        &self,
        solver: &'a Solver<D, RT>,
    ) -> DisplayUnsat<'a, D> {
        let graph = self.graph(solver);
        DisplayUnsat::new(graph, solver.provider())
    }
}

/// A node in the graph representation of a [`Conflict`]
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum ConflictNode<S = SolvableId> {
    /// Node corresponding to the synthetic solver root
    Root,
    /// Node corresponding to a solvable
    Solvable(S),
    /// Node representing a dependency without candidates
    UnresolvedDependency,
    /// Node representing an exclude reason
    Excluded(StringId),
}

impl<S> ConflictNode<S> {
    fn from_solvable_or_root(solvable_id: SolvableIdOrRoot<S>) -> Self {
        match solvable_id {
            SolvableIdOrRoot::Root => Self::Root,
            SolvableIdOrRoot::Solvable(solvable_id) => Self::Solvable(solvable_id),
        }
    }

    fn solvable_or_root(self) -> SolvableIdOrRoot<S> {
        match self {
            ConflictNode::Root => SolvableIdOrRoot::root(),
            ConflictNode::Solvable(solvable_id) => solvable_id.into(),
            ConflictNode::UnresolvedDependency => {
                panic!("expected solvable node, found unresolved dependency")
            }
            ConflictNode::Excluded(_) => {
                panic!("expected solvable node, found excluded node")
            }
        }
    }

    fn solvable(self) -> Option<S> {
        match self {
            ConflictNode::Solvable(solvable_id) => Some(solvable_id),
            ConflictNode::Root | ConflictNode::UnresolvedDependency | ConflictNode::Excluded(_) => {
                None
            }
        }
    }
}

/// An edge in the graph representation of a [`Conflict`]
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum ConflictEdge<S = SolvableId> {
    /// The target node is a candidate for the dependency specified by the
    /// [`Requirement`]
    Requires(Requirement),
    /// The target node is involved in a conflict, caused by `ConflictCause`
    Conflict(ConflictCause<S>),
}

impl<S> ConflictEdge<S> {
    fn try_requires(self) -> Option<Requirement> {
        match self {
            ConflictEdge::Requires(match_spec_id) => Some(match_spec_id),
            ConflictEdge::Conflict(_) => None,
        }
    }

    fn requires(self) -> Requirement {
        match self {
            ConflictEdge::Requires(match_spec_id) => match_spec_id,
            ConflictEdge::Conflict(_) => panic!("expected requires edge, found conflict"),
        }
    }
}

/// Conflict causes
#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum ConflictCause<S = SolvableId> {
    /// The solvable is locked
    Locked(S),
    /// The target node is constrained by the specified version set
    Constrains(VersionSetId),
    /// It is forbidden to install multiple instances of the same dependency
    ForbidMultipleInstances,
    /// The node was excluded
    Excluded,
}

/// Represents a node that has been merged with others
///
/// Merging is done to simplify error messages, and happens when a group of
/// nodes satisfies the following criteria:
///
/// - They all have the same name
/// - They all have the same predecessor nodes
/// - They all have the same successor nodes
pub struct MergedConflictNode<S = SolvableId> {
    /// The list of solvable ids that have been merged into this node.
    pub ids: Vec<S>,
}

/// Graph representation of [`Conflict`]
///
/// The root of the graph is the "root solvable". Note that not all the
/// solvable's requirements are included in the graph, only those that are
/// directly or indirectly involved in the conflict.
#[derive(Clone)]
pub struct ConflictGraph<S = SolvableId> {
    /// The conflict graph as a directed petgraph.
    pub graph: DiGraph<ConflictNode<S>, ConflictEdge<S>>,
    /// The single source node for root constraints introduced to the solver.
    pub root_node: NodeIndex,
    /// A single sink node that consumes all unresolvable constraints.
    pub unresolved_node: Option<NodeIndex>,
}

impl<S: SolverId> ConflictGraph<S> {
    /// Writes a graphviz graph that represents this instance to the specified
    /// output.
    pub fn graphviz(
        &self,
        f: &mut impl std::io::Write,
        interner: &impl Interner<SolvableId = S>,
        simplify: bool,
    ) -> Result<(), std::io::Error> {
        let graph = &self.graph;

        let merged_nodes = if simplify {
            self.simplify(interner)
        } else {
            HashMap::default()
        };

        write!(f, "digraph {{")?;
        for nx in graph.node_indices() {
            let id = match graph.node_weight(nx).as_ref().unwrap() {
                ConflictNode::Root | ConflictNode::Solvable(_) => {
                    graph.node_weight(nx).unwrap().solvable_or_root()
                }
                _ => continue,
            };

            // If this is a merged node, skip it unless it is the first one in the group
            if let Some(solvable_id) = id.solvable() {
                if let Some(merged) = merged_nodes.get(&solvable_id) {
                    if solvable_id != merged.ids[0] {
                        continue;
                    }
                }
            }

            let mut added_edges = Vec::new();
            for edge in graph.edges_directed(nx, Direction::Outgoing) {
                let target = *graph.node_weight(edge.target()).unwrap();

                let color = match edge.weight() {
                    ConflictEdge::Requires(_) if target != ConflictNode::UnresolvedDependency => {
                        "black"
                    }
                    _ => "red",
                };

                let label = match edge.weight() {
                    ConflictEdge::Requires(requirement) => {
                        requirement.display(interner).to_string()
                    }
                    ConflictEdge::Conflict(ConflictCause::Constrains(version_set_id)) => {
                        interner.display_version_set(*version_set_id).to_string()
                    }
                    ConflictEdge::Conflict(ConflictCause::ForbidMultipleInstances)
                    | ConflictEdge::Conflict(ConflictCause::Locked(_)) => {
                        "already installed".to_string()
                    }
                    ConflictEdge::Conflict(ConflictCause::Excluded) => "excluded".to_string(),
                };

                let target = match target {
                    ConflictNode::Root | ConflictNode::Solvable(_) => {
                        let mut solvable_2 = target.solvable_or_root();
                        // If the target node has been merged, replace it by the first id in the
                        // group
                        if let Some(solvable_id) = solvable_2.solvable() {
                            if let Some(merged) = merged_nodes.get(&solvable_id) {
                                solvable_2 = merged.ids[0].into();

                                // Skip the edge if we would be adding a duplicate
                                if added_edges.contains(&solvable_2) {
                                    continue;
                                }
                                added_edges.push(solvable_2);
                            }
                        }

                        solvable_2.display(interner).to_string()
                    }
                    ConflictNode::UnresolvedDependency => "unresolved".to_string(),
                    ConflictNode::Excluded(reason) => {
                        format!("reason: {}", interner.display_string(reason))
                    }
                };

                write!(
                    f,
                    "\"{}\" -> \"{}\"[color={color}, label=\"{label}\"];",
                    id.display(interner),
                    target
                )?;
            }
        }
        write!(f, "}}")
    }

    /// Simplifies and collapses nodes so that these can be considered the same
    /// candidate
    pub fn simplify(
        &self,
        interner: &impl Interner<SolvableId = S>,
    ) -> HashMap<S, Rc<MergedConflictNode<S>>> {
        let graph = &self.graph;

        // Gather information about nodes that can be merged
        let mut maybe_merge = HashMap::default();
        for node_id in graph.node_indices() {
            let candidate = match graph[node_id] {
                ConflictNode::Solvable(solvable_id) => solvable_id,
                ConflictNode::Root
                | ConflictNode::UnresolvedDependency
                | ConflictNode::Excluded(_) => continue,
            };

            // Candidates that require different version sets stay separate so each
            // distinct requirement is reported to the user (conda/rattler#2476).
            // `ForbidMultipleInstances` edges chain every candidate of the same
            // package name together, which makes each candidate's neighbourhood
            // unique and prevents any merging at all. They carry no information
            // that distinguishes one candidate from another, so ignore them.
            let is_forbid_multiple = |w: &ConflictEdge<S>| {
                matches!(
                    w,
                    ConflictEdge::Conflict(ConflictCause::ForbidMultipleInstances)
                )
            };
            let predecessors: Vec<_> = graph
                .edges_directed(node_id, Direction::Incoming)
                .filter(|e| !is_forbid_multiple(e.weight()))
                .map(|e| (e.weight().try_requires(), e.source()))
                .sorted_unstable()
                .collect();
            let successors: Vec<_> = graph
                .edges(node_id)
                .filter(|e| !is_forbid_multiple(e.weight()))
                .map(|e| (e.weight().try_requires(), e.target()))
                .sorted_unstable()
                .collect();

            let name = interner
                .display_name(interner.solvable_name(candidate))
                .to_string();

            let entry = maybe_merge
                .entry((name, predecessors, successors))
                .or_insert(Vec::new());

            entry.push((node_id, candidate));
        }

        let mut merged_candidates = HashMap::default();
        for m in maybe_merge.into_values() {
            if m.len() > 1 {
                let m = Rc::new(MergedConflictNode {
                    ids: m.into_iter().map(|(_, snd)| snd).collect(),
                });
                for &id in &m.ids {
                    merged_candidates.insert(id, m.clone());
                }
            }
        }

        merged_candidates
    }

    fn get_installable_set(&self) -> HashSet<NodeIndex> {
        let mut installable = HashSet::new();

        // Definition: a package is installable if it does not have any outgoing
        // conflicting edges and if each of its dependencies has at least one
        // installable option.

        // Algorithm: propagate installability bottom-up
        let mut dfs = DfsPostOrder::new(&self.graph, self.root_node);
        'outer_loop: while let Some(nx) = dfs.next(&self.graph) {
            if self.unresolved_node == Some(nx) {
                // The unresolved node isn't installable
                continue;
            }

            // Determine any incoming "exclude" edges to the node. This would indicate that
            // the node is disabled for external reasons.
            let excluding_edges = self
                .graph
                .edges_directed(nx, Direction::Incoming)
                .any(|e| matches!(e.weight(), ConflictEdge::Conflict(ConflictCause::Excluded)));
            if excluding_edges {
                // Nodes with incoming disabling edges aren't installable
                continue;
            }

            let outgoing_conflicts = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .any(|e| matches!(e.weight(), ConflictEdge::Conflict(_)));
            if outgoing_conflicts {
                // Nodes with outgoing conflicts aren't installable
                continue;
            }

            // Edges grouped by dependency
            let dependencies = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|e| match e.weight() {
                    ConflictEdge::Requires(version_set_id) => (version_set_id, e.target()),
                    ConflictEdge::Conflict(_) => unreachable!(),
                })
                .chunk_by(|(version_set_id, _)| *version_set_id);

            for (_, mut deps) in &dependencies {
                if deps.all(|(_, target)| !installable.contains(&target)) {
                    // No installable options for this dep
                    continue 'outer_loop;
                }
            }

            // The package is installable!
            installable.insert(nx);
        }

        installable
    }

    fn get_missing_set(&self) -> HashSet<NodeIndex> {
        // Definition: a package is missing if it is not involved in any conflicts, yet
        // it is not installable

        let mut missing = HashSet::new();
        match self.unresolved_node {
            None => return missing,
            Some(nx) => missing.insert(nx),
        };

        // Algorithm: propagate missing bottom-up
        let mut dfs = DfsPostOrder::new(&self.graph, self.root_node);
        while let Some(nx) = dfs.next(&self.graph) {
            let outgoing_conflicts = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .any(|e| matches!(e.weight(), ConflictEdge::Conflict(_)));
            if outgoing_conflicts {
                // Nodes with outgoing conflicts aren't missing
                continue;
            }

            // Edges grouped by dependency
            let dependencies = self
                .graph
                .edges_directed(nx, Direction::Outgoing)
                .map(|e| match e.weight() {
                    ConflictEdge::Requires(version_set_id) => (version_set_id, e.target()),
                    ConflictEdge::Conflict(_) => unreachable!(),
                })
                .chunk_by(|(version_set_id, _)| *version_set_id);

            // Missing if at least one dependency is missing
            if dependencies
                .into_iter()
                .any(|(_, mut deps)| deps.all(|(_, target)| missing.contains(&target)))
            {
                missing.insert(nx);
            }
        }

        missing
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum ChildOrder {
    HasRemainingSiblings,
    Last,
}

struct Indenter {
    levels: Vec<ChildOrder>,
    top_level_indent: bool,
}

impl Indenter {
    fn new(top_level_indent: bool) -> Self {
        Self {
            levels: Vec::new(),
            top_level_indent,
        }
    }

    fn is_at_top_level(&self) -> bool {
        self.levels.len() == 1
    }

    fn push_level(&self) -> Self {
        self.push_level_with_order(ChildOrder::HasRemainingSiblings)
    }

    fn push_level_with_order(&self, order: ChildOrder) -> Self {
        let mut levels = self.levels.clone();
        levels.push(order);
        Self {
            levels,
            top_level_indent: self.top_level_indent,
        }
    }

    fn set_last(&mut self) {
        *self.levels.last_mut().unwrap() = ChildOrder::Last;
    }

    fn get_indent(&self) -> String {
        assert!(!self.levels.is_empty());

        let mut s = String::new();

        let deepest_level = self.levels.len() - 1;

        for (level, &order) in self.levels.iter().enumerate() {
            if level == 0 && !self.top_level_indent {
                // Skip
                continue;
            }

            let is_at_deepest_level = level == deepest_level;

            let tree_prefix = match (is_at_deepest_level, order) {
                (true, ChildOrder::HasRemainingSiblings) => "├─",
                (true, ChildOrder::Last) => "└─",
                (false, ChildOrder::HasRemainingSiblings) => "│ ",
                (false, ChildOrder::Last) => "  ",
            };

            // TODO: are these the right characters? Alternatives: https://en.wikipedia.org/wiki/Box-drawing_character or look at mamba

            s.push_str(tree_prefix);
            s.push(' ');
        }

        s
    }
}

/// The number of parents a candidate's subtree is repeated under.
///
/// Repeating it lets every branch of the report be read on its own, but a
/// candidate that a great many parents require would otherwise bury the report
/// in copies of the same lines; past this many, the remaining parents point at
/// the copies already printed.
const MAX_REPEATED_SUBTREES: usize = 4;

/// The candidates the report descended through to reach a line, and the
/// requirement it followed out of each of them.
///
/// It says which requirements have to hold at the same time as the line, and it
/// identifies the line itself: the same requirement is printed once per branch
/// that leads to it, and those are different lines.
type LinePath = Vec<(NodeIndex, Requirement)>;

/// The labels a report puts in front of the requirement lines its conflict
/// messages point at, so that the reader can find them: `(A) nodejs 22.*` is
/// pointed at by `..., which conflicts with 20.* (B) and 22.* (A)`.
///
/// A message can point at a line that is only printed further down, so the
/// report is written twice: the first pass collects which lines are pointed at
/// and the order they appear in, and the second one prints with the labels.
#[derive(Default)]
struct Anchors {
    /// Set once the labels have been handed out and the report is being printed.
    printing: bool,
    /// The requirement lines, in the order they are printed.
    order: Vec<LinePath>,
    /// The lines a conflict message points at.
    referenced: HashSet<LinePath>,
    /// The position in the label sequence a line was handed, if it was.
    labels: HashMap<LinePath, usize>,
}

impl Anchors {
    /// Notes a requirement line, in the order the report prints it.
    fn note_line(&mut self, line: &LinePath) {
        if !self.printing {
            self.order.push(line.clone());
        }
    }

    /// Notes that a conflict message points at a requirement line.
    fn note_reference(&mut self, line: &LinePath) {
        if !self.printing {
            self.referenced.insert(line.clone());
        }
    }

    /// Hands a label to every line that is pointed at, in the order the lines
    /// appear, and switches to printing.
    fn assign_labels(&mut self) {
        self.labels = self
            .order
            .iter()
            .filter(|line| self.referenced.contains(*line))
            .enumerate()
            .map(|(index, line)| (line.clone(), index))
            .collect();
        self.printing = true;
    }

    /// Where a line sits in the label sequence, for listing mentions of several
    /// lines in the order the report prints them.
    fn label_index(&self, line: &LinePath) -> Option<usize> {
        self.labels.get(line).copied()
    }

    /// `(A) `, to put in front of a requirement line that is pointed at.
    fn prefix(&self, line: &LinePath) -> String {
        match self.labels.get(line) {
            Some(&index) => format!("({label}) ", label = label_for(index)),
            None => String::new(),
        }
    }

    /// ` (A)`, to put after a mention of a requirement line.
    fn suffix(&self, line: Option<&LinePath>) -> String {
        match line.and_then(|line| self.labels.get(line)) {
            Some(&index) => format!(" ({label})", label = label_for(index)),
            None => String::new(),
        }
    }
}

/// The `index`th label: `A`, `B`, .., `Z`, `AA`, `AB`, ..
fn label_for(index: usize) -> String {
    let mut label = String::new();
    let mut index = index;
    loop {
        label.insert(0, char::from(b'A' + (index % 26) as u8));
        if index < 26 {
            return label;
        }
        index = index / 26 - 1;
    }
}

/// A struct implementing [`fmt::Display`] that generates a user-friendly
/// representation of a conflict graph
pub struct DisplayUnsat<'i, I: Interner> {
    graph: ConflictGraph<I::SolvableId>,
    merged_candidates: HashMap<I::SolvableId, Rc<MergedConflictNode<I::SolvableId>>>,
    nodes_by_solvable: HashMap<I::SolvableId, NodeIndex>,
    installable_set: HashSet<NodeIndex>,
    missing_set: HashSet<NodeIndex>,
    interner: &'i I,
}

impl<'i, I: Interner> DisplayUnsat<'i, I> {
    pub(crate) fn new(graph: ConflictGraph<I::SolvableId>, interner: &'i I) -> Self {
        let merged_candidates = graph.simplify(interner);
        let nodes_by_solvable = graph
            .graph
            .node_indices()
            .filter_map(|node| graph.graph[node].solvable().map(|id| (id, node)))
            .collect();
        let installable_set = graph.get_installable_set();
        let missing_set = graph.get_missing_set();

        Self {
            graph,
            merged_candidates,
            nodes_by_solvable,
            installable_set,
            missing_set,
            interner,
        }
    }

    /// Whether a candidate is unusable because a different version of the same
    /// package is required elsewhere.
    ///
    /// The [`ConflictCause::ForbidMultipleInstances`] clauses form a chain over
    /// all candidates of a package, so a candidate takes part in such a conflict
    /// whether the edge points at it or away from it; only looking at outgoing
    /// edges misses the last link of the chain. Installable candidates sit in
    /// that chain too, but they are presented as viable options and must not be
    /// blamed for it.
    fn conflicts_with_other_versions(&self, candidate: NodeIndex) -> bool {
        let graph = &self.graph.graph;
        !self.installable_set.contains(&candidate)
            && graph
                .edges_directed(candidate, Direction::Outgoing)
                .chain(graph.edges_directed(candidate, Direction::Incoming))
                .any(|e| {
                    e.weight() == &ConflictEdge::Conflict(ConflictCause::ForbidMultipleInstances)
                })
    }

    /// The solvables a candidate has been merged with, or just the candidate
    /// itself if it stands alone.
    fn group_of<'a>(&'a self, solvable_id: &'a I::SolvableId) -> &'a [I::SolvableId] {
        self.merged_candidates
            .get(solvable_id)
            .map_or(std::slice::from_ref(solvable_id), |merged| {
                merged.ids.as_slice()
            })
    }

    /// The node a line path keys a candidate on.
    ///
    /// Candidates that have been merged are printed as one line and only one of
    /// them is descended into, but a path that leads through the group can arrive
    /// at any of its members. They all have the same requirements, so keying every
    /// member on the same node makes a path built while looking for conflicts
    /// match the line the report prints.
    fn canonical_node(&self, node: NodeIndex) -> NodeIndex {
        self.graph.graph[node]
            .solvable()
            .and_then(|id| self.nodes_by_solvable.get(&self.group_of(&id)[0]).copied())
            .unwrap_or(node)
    }

    /// The name of the package a candidate is a version of, as it is displayed.
    fn package_name_of(&self, candidate: NodeIndex) -> Option<String> {
        let solvable_id = self.graph.graph[candidate].solvable()?;
        let name = self.interner.solvable_name(solvable_id);
        Some(self.interner.display_name(name).to_string())
    }

    /// Describes a candidate, naming every version it has been merged with.
    fn display_candidate(&self, solvable_id: I::SolvableId) -> String {
        self.interner
            .display_merged_solvables(self.group_of(&solvable_id))
            .to_string()
    }

    /// Returns the reason a solvable was excluded, if it was.
    fn excluded_reason(&self, solvable_id: I::SolvableId) -> Option<StringId> {
        let graph = &self.graph.graph;
        let node = graph
            .node_indices()
            .find(|&node| graph[node] == ConflictNode::Solvable(solvable_id))?;
        graph.edges(node).find_map(|e| match e.weight() {
            ConflictEdge::Conflict(ConflictCause::Excluded) => match graph[e.target()] {
                ConflictNode::Excluded(reason) => Some(reason),
                _ => unreachable!("an excluded edge must point to an excluded node"),
            },
            _ => None,
        })
    }

    /// The other candidates of the same package that this report also asks for,
    /// one solvable per merge group.
    ///
    /// Only one version of a package can be installed at a time, so a candidate
    /// that takes part in a [`ConflictCause::ForbidMultipleInstances`] conflict
    /// is unusable because some other version of it is required elsewhere.
    /// Naming those versions tells the user which requirements cannot be
    /// satisfied together, instead of leaving them to guess.
    fn conflicting_candidates(&self, candidate: NodeIndex) -> Vec<I::SolvableId> {
        let graph = &self.graph.graph;
        let Some(solvable_id) = graph[candidate].solvable() else {
            return Vec::new();
        };
        let name = self.interner.solvable_name(solvable_id);

        // The candidate's own merge group is not a rival: only one of its members
        // has to be installable for the group to be usable.
        let mut seen: HashSet<I::SolvableId> =
            self.group_of(&solvable_id).iter().copied().collect();
        let mut rivals = Vec::new();
        for rival in graph
            .node_indices()
            .filter_map(|node| graph[node].solvable())
            .filter(|&id| self.interner.solvable_name(id) == name)
        {
            // Report every merge group once, no matter which of its members is
            // encountered first.
            if seen.contains(&rival) {
                continue;
            }
            seen.extend(self.group_of(&rival).iter().copied());
            rivals.push(rival);
        }

        // The graph's node order is an implementation detail; sort so the message
        // is stable and the versions read in a predictable order.
        rivals.sort_unstable_by_key(|&id| self.display_candidate(id));
        rivals
    }

    /// The requirements that ask for another version of the candidate's package,
    /// given the path the report took to reach it.
    ///
    /// Every candidate of a package rules out all the others, but most of those
    /// are asked for somewhere else entirely, or by an alternative that does not
    /// have to be picked. The ones that make *this* candidate unusable are the
    /// ones the other requirements of the candidates on the path lead to: those
    /// have to hold at the same time as the requirement that led here.
    ///
    /// The requirement is named rather than the versions it resolves to, because
    /// it says in the user's own terms what cannot be met at the same time, and
    /// it is spelled out somewhere else in the report anyway. Each one comes with
    /// the line that spells it out, so that the message can point at it.
    fn conflicting_requirements_on_path(
        &self,
        candidate: NodeIndex,
        path: &[(NodeIndex, Requirement)],
    ) -> Vec<(String, LinePath)> {
        let graph = &self.graph.graph;
        let Some(solvable_id) = graph[candidate].solvable() else {
            return Vec::new();
        };
        let name = self.interner.solvable_name(solvable_id);

        // The candidate's own merge group is not a rival: only one of its members
        // has to be installable for the group to be usable.
        let mut seen: HashSet<I::SolvableId> =
            self.group_of(&solvable_id).iter().copied().collect();
        let mut rivals = Vec::new();
        for (index, &(ancestor, taken)) in path.iter().enumerate() {
            // Walk everything the sibling requirements of this ancestor lead to.
            // Alternatives of the requirement that led here are not rivals: only
            // one of them has to be installable.
            let mut queue: Vec<(NodeIndex, LinePath)> = graph
                .edges(ancestor)
                .filter_map(|e| {
                    let requirement = e.weight().try_requires()?;
                    if requirement == taken {
                        return None;
                    }
                    // The sibling is printed where this ancestor is, so its line
                    // is the path that led here with the sibling followed instead.
                    let mut line = path[..index].to_vec();
                    line.push((ancestor, requirement));
                    Some((e.target(), line))
                })
                .collect();
            let mut visited: HashSet<NodeIndex> = queue.iter().map(|(node, _)| *node).collect();
            while let Some((node, line)) = queue.pop() {
                if let Some(id) = graph[node].solvable() {
                    if self.interner.solvable_name(id) == name && !seen.contains(&id) {
                        seen.extend(self.group_of(&id).iter().copied());
                        let (_, requirement) = *line.last().expect("a line names a requirement");
                        rivals.push((requirement.display(self.interner).to_string(), line.clone()));
                    }
                }
                for edge in graph.edges(node) {
                    let Some(requirement) = edge.weight().try_requires() else {
                        continue;
                    };
                    if visited.insert(edge.target()) {
                        let mut line = line.clone();
                        line.push((self.canonical_node(node), requirement));
                        queue.push((edge.target(), line));
                    }
                }
            }
        }

        // The graph's edge order is an implementation detail; sort so the message
        // is stable, and name a requirement that several candidates match once.
        rivals.sort_unstable();
        rivals.dedup_by(|(a, _), (b, _)| a == b);
        rivals
    }

    /// Writes the report, once to work out the labels and once for real.
    fn fmt_graph(
        &self,
        f: &mut Formatter<'_>,
        top_level_edges: &[EdgeReference<'_, ConflictEdge<I::SolvableId>>],
        top_level_indent: bool,
    ) -> fmt::Result {
        let mut anchors = Anchors::default();
        self.write_graph(
            &mut String::new(),
            top_level_edges,
            top_level_indent,
            &mut anchors,
        )?;
        anchors.assign_labels();
        self.write_graph(f, top_level_edges, top_level_indent, &mut anchors)
    }

    fn write_graph(
        &self,
        w: &mut dyn fmt::Write,
        top_level_edges: &[EdgeReference<'_, ConflictEdge<I::SolvableId>>],
        top_level_indent: bool,
        anchors: &mut Anchors,
    ) -> fmt::Result {
        pub enum DisplayOp {
            Requirement(Requirement, Vec<EdgeIndex>),
            Candidate(NodeIndex),
        }

        let graph = &self.graph.graph;
        let installable_nodes = &self.installable_set;

        // How often the subtree below a candidate has been spelled out already.
        let mut expanded: HashMap<SolvableIdOrRoot<I::SolvableId>, usize> = HashMap::default();

        // The candidates the printer descended through to reach a stack entry, and
        // the requirement it followed out of each of them. Used to tell which
        // requirements have to hold at the same time.
        type Path = Rc<Vec<(NodeIndex, Requirement)>>;

        // Note: we are only interested in requires edges here
        let indenter = Indenter::new(top_level_indent);
        let mut stack = top_level_edges
            .iter()
            .filter(|e| e.weight().try_requires().is_some())
            .chunk_by(|e| e.weight().requires())
            .into_iter()
            .map(|(version_set_id, group)| {
                let edges: Vec<_> = group.map(|e| e.id()).collect();
                (version_set_id, edges)
            })
            .sorted_by_key(|(_version_set_id, edges)| {
                edges
                    .iter()
                    .any(|&edge| installable_nodes.contains(&graph.edge_endpoints(edge).unwrap().1))
            })
            .map(|(version_set_id, edges)| {
                (
                    DisplayOp::Requirement(version_set_id, edges),
                    indenter.push_level(),
                    Rc::new(vec![(self.graph.root_node, version_set_id)]) as Path,
                )
            })
            .collect::<Vec<_>>();

        if !stack.is_empty() {
            // Mark the first element of the stack as not having any remaining siblings
            stack[0].1.set_last();
        }

        while let Some((node, indenter, path)) = stack.pop() {
            let top_level = indenter.is_at_top_level();
            let indent = indenter.get_indent();

            match node {
                DisplayOp::Requirement(requirement, edges) => {
                    debug_assert!(!edges.is_empty());

                    let installable = edges.iter().any(|&e| {
                        let (_, target) = graph.edge_endpoints(e).unwrap();
                        installable_nodes.contains(&target)
                    });

                    let req = requirement.display(self.interner).to_string();

                    // This line is what a conflict message elsewhere in the report
                    // points at, if it needs a version this requirement rules out.
                    let anchor = anchors.prefix(&path);
                    anchors.note_line(&path);

                    let target_nx = graph.edge_endpoints(edges[0]).unwrap().1;
                    let missing =
                        edges.len() == 1 && graph[target_nx] == ConflictNode::UnresolvedDependency;
                    if missing {
                        // No candidates for requirement
                        if top_level {
                            writeln!(w, "{indent}No candidates were found for {anchor}{req}.")?;
                        } else {
                            writeln!(
                                w,
                                "{indent}{anchor}{req}, for which no candidates were found.",
                            )?;
                        }
                    } else if installable {
                        // Package can be installed (only mentioned for top-level requirements)
                        if top_level {
                            writeln!(
                                w,
                                "{indent}{anchor}{req} can be installed with any of the following options:"
                            )?;
                        } else {
                            writeln!(
                                w,
                                "{indent}{anchor}{req}, which can be installed with any of the following options:"
                            )?;
                        }

                        let children: Vec<_> = edges
                            .iter()
                            .filter(|&&e| {
                                installable_nodes.contains(&graph.edge_endpoints(e).unwrap().1)
                            })
                            .map(|&e| {
                                (
                                    DisplayOp::Candidate(graph.edge_endpoints(e).unwrap().1),
                                    indenter.push_level(),
                                    path.clone(),
                                )
                            })
                            .collect();

                        // TODO: this is an utterly ugly hack that should be burnt to ashes
                        let mut deduplicated_children = Vec::new();
                        let mut merged_and_seen = HashSet::new();
                        for child in children {
                            let (DisplayOp::Candidate(child_node), _, _) = child else {
                                unreachable!()
                            };
                            let solvable_id = graph[child_node].solvable_or_root();
                            let Some(solvable_id) = solvable_id.solvable() else {
                                continue;
                            };

                            let merged = self.merged_candidates.get(&solvable_id);

                            // Skip merged stuff that we have already seen
                            if merged_and_seen.contains(&solvable_id) {
                                continue;
                            }

                            if let Some(merged) = merged {
                                merged_and_seen.extend(merged.ids.iter().copied())
                            }

                            deduplicated_children.push(child);
                        }

                        if !deduplicated_children.is_empty() {
                            deduplicated_children[0].1.set_last();
                        }

                        stack.extend(deduplicated_children);
                    } else {
                        // Package cannot be installed (the conflicting requirement is further down
                        // the tree)
                        if top_level {
                            writeln!(
                                w,
                                "{indent}{anchor}{req} cannot be installed because there are no viable options:"
                            )?;
                        } else {
                            writeln!(
                                w,
                                "{indent}{anchor}{req}, which cannot be installed because there are no viable options:"
                            )?;
                        }

                        let children: Vec<_> = edges
                            .iter()
                            .map(|&e| {
                                (
                                    DisplayOp::Candidate(graph.edge_endpoints(e).unwrap().1),
                                    indenter.push_level(),
                                    path.clone(),
                                )
                            })
                            .collect();

                        // TODO: this is an utterly ugly hack that should be burnt to ashes
                        let mut deduplicated_children = Vec::new();
                        let mut merged_and_seen = HashSet::new();
                        for child in children {
                            let (DisplayOp::Candidate(child_node), _, _) = child else {
                                unreachable!()
                            };
                            let Some(solvable_id) = graph[child_node].solvable() else {
                                continue;
                            };
                            let merged = self.merged_candidates.get(&solvable_id);

                            // Skip merged stuff that we have already seen
                            if merged_and_seen.contains(&solvable_id) {
                                continue;
                            }

                            if let Some(merged) = merged {
                                merged_and_seen.extend(merged.ids.iter().copied())
                            }

                            deduplicated_children.push(child);
                        }

                        if !deduplicated_children.is_empty() {
                            deduplicated_children[0].1.set_last();
                        }

                        stack.extend(deduplicated_children);
                    }
                }
                DisplayOp::Candidate(candidate) => {
                    let solvable_id = graph[candidate].solvable_or_root();

                    let version = match solvable_id.solvable() {
                        Some(id) => self.display_candidate(id),
                        None => "<root>".to_string(),
                    };

                    // A candidate reachable through several parents is printed
                    // below each of them, so that every branch can be read on its
                    // own. Two things have to cut that off: a circular dependency,
                    // whose subtree would never end, and a candidate pulled in by
                    // very many parents, which would bury the report in copies.
                    let repeats_ancestor = path.iter().any(|&(ancestor, _)| {
                        match (graph[ancestor].solvable(), solvable_id.solvable()) {
                            (Some(ancestor), Some(id)) => self.group_of(&id).contains(&ancestor),
                            _ => false,
                        }
                    });
                    // A candidate without requirements of its own is a single line;
                    // pointing at an earlier copy of it saves nothing.
                    let repeated_too_often = graph
                        .edges(candidate)
                        .any(|e| e.weight().try_requires().is_some())
                        && {
                            let printed = expanded.entry(solvable_id).or_insert(0);
                            *printed += 1;
                            *printed > MAX_REPEATED_SUBTREES
                        };
                    if repeats_ancestor || repeated_too_often {
                        writeln!(w, "{indent}{version}, as reported above")?;
                        continue;
                    }

                    let excluded = graph
                        .edges_directed(candidate, Direction::Outgoing)
                        .find_map(|e| match e.weight() {
                            ConflictEdge::Conflict(ConflictCause::Excluded) => {
                                let ConflictNode::Excluded(reason) = graph[e.target()] else {
                                    unreachable!();
                                };
                                Some(reason)
                            }
                            _ => None,
                        });
                    let already_installed = self.conflicts_with_other_versions(candidate);
                    let constrains_conflict = graph.edges(candidate).any(|e| {
                        matches!(
                            e.weight(),
                            ConflictEdge::Conflict(ConflictCause::Constrains(_))
                        )
                    });
                    let is_leaf = graph.edges(candidate).next().is_none();

                    if let Some(excluded_reason) = excluded {
                        writeln!(
                            w,
                            "{indent}{version} is excluded because {reason}",
                            reason = self.interner.display_string(excluded_reason),
                        )?;
                    } else if already_installed {
                        // Spell out *what* these candidates are unusable with: a
                        // package can only be present once, so name the other
                        // requirements for it that have to hold at the same time.
                        let mut rivals: Vec<(String, Option<LinePath>)> = self
                            .conflicting_requirements_on_path(candidate, &path)
                            .into_iter()
                            .map(|(req, line)| (req, Some(line)))
                            .collect();
                        if rivals.is_empty() {
                            // The conflict is with a version required outside of
                            // the path that led here, so fall back to naming every
                            // other version in the report.
                            rivals = self
                                .conflicting_candidates(candidate)
                                .into_iter()
                                .map(|id| (self.display_candidate(id), None))
                                .collect();
                        }

                        // Point at the lines the requirements are spelled out on,
                        // so that the reader can find them.
                        for (_, line) in &rivals {
                            if let Some(line) = line {
                                anchors.note_reference(line);
                            }
                        }

                        // List them in the order the report prints the lines they
                        // point at, so that the labels run in one direction.
                        // Requirements without a line to point at keep their
                        // place at the end, sorted by what they say.
                        rivals.sort_by_cached_key(|(req, line)| {
                            let label = line
                                .as_ref()
                                .and_then(|line| anchors.label_index(line))
                                .unwrap_or(usize::MAX);
                            (label, req.clone())
                        });

                        // Every rival is a requirement on the same package as the
                        // candidate, so name it once in front of the list rather
                        // than repeating it before every entry.
                        let lead = self
                            .package_name_of(candidate)
                            .map(|name| format!("{name} "))
                            .filter(|lead| {
                                rivals.iter().all(|(req, _)| req.starts_with(lead.as_str()))
                            });
                        let rivals = rivals
                            .iter()
                            .map(|(req, line)| {
                                let req = match &lead {
                                    Some(lead) => &req[lead.len()..],
                                    None => req.as_str(),
                                };
                                format!("{req}{label}", label = anchors.suffix(line.as_ref()))
                            })
                            .collect_vec();
                        let lead = lead.as_deref().unwrap_or_default();
                        match rivals.as_slice() {
                            [] => writeln!(
                                w,
                                "{indent}{version}, which conflicts with the versions reported above."
                            )?,
                            [rival] => writeln!(
                                w,
                                "{indent}{version}, which conflicts with {lead}{rival}"
                            )?,
                            [rivals @ .., last] => writeln!(
                                w,
                                "{indent}{version}, which conflicts with {lead}{rivals} and {last}",
                                rivals = rivals.iter().format(", "),
                            )?,
                        }
                    } else if is_leaf {
                        writeln!(w, "{indent}{version}")?;
                    } else if constrains_conflict {
                        let mut version_sets = graph
                            .edges(candidate)
                            .flat_map(|e| match e.weight() {
                                ConflictEdge::Conflict(ConflictCause::Constrains(
                                    version_set_id,
                                )) => Some(version_set_id),
                                _ => None,
                            })
                            .dedup()
                            .peekable();

                        writeln!(w, "{indent}{version} would constrain",)?;

                        let mut indenter = indenter.push_level();
                        while let Some(&version_set_id) = version_sets.next() {
                            let name = self
                                .interner
                                .display_name(self.interner.version_set_name(version_set_id));
                            let version_set = self.interner.display_version_set(version_set_id);

                            if version_sets.peek().is_none() {
                                indenter.set_last();
                            }
                            let indent = indenter.get_indent();
                            writeln!(
                                w,
                                "{indent}{name} {version_set}, which conflicts with any installable versions previously reported",
                            )?;
                        }
                    } else {
                        writeln!(w, "{indent}{version} would require",)?;
                        let mut requirements = graph
                            .edges(candidate)
                            .chunk_by(|e| e.weight().requires())
                            .into_iter()
                            .map(|(version_set_id, group)| {
                                let edges: Vec<_> = group.map(|e| e.id()).collect();
                                (version_set_id, edges)
                            })
                            .sorted_by_key(|(_version_set_id, edges)| {
                                edges.iter().any(|&edge| {
                                    installable_nodes
                                        .contains(&graph.edge_endpoints(edge).unwrap().1)
                                })
                            })
                            .map(|(version_set_id, edges)| {
                                let mut descended = (*path).clone();
                                descended.push((self.canonical_node(candidate), version_set_id));
                                (
                                    DisplayOp::Requirement(version_set_id, edges),
                                    indenter.push_level(),
                                    Rc::new(descended) as Path,
                                )
                            })
                            .collect::<Vec<_>>();

                        if !requirements.is_empty() {
                            requirements[0].1.set_last();
                        }

                        stack.extend(requirements);
                    }
                }
            }
        }

        Ok(())
    }
}

impl<I: Interner> fmt::Display for DisplayUnsat<'_, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let (top_level_missing, top_level_conflicts): (Vec<_>, _) = self
            .graph
            .graph
            .edges(self.graph.root_node)
            .partition(|e| self.missing_set.contains(&e.target()));

        if !top_level_missing.is_empty() {
            self.fmt_graph(f, &top_level_missing, false)?;
        }

        if !top_level_conflicts.is_empty() {
            writeln!(f, "The following packages are incompatible")?;
            self.fmt_graph(f, &top_level_conflicts, true)?;

            // Conflicts caused by locked dependencies. Every `Lock` clause
            // produces its own root edge, one per forbidden candidate, so the
            // lines are deduplicated by the solvable that is locked.
            let mut reported_locked = HashSet::new();
            let mut lines = Vec::new();
            for e in self.graph.graph.edges(self.graph.root_node) {
                let conflict = match e.weight() {
                    ConflictEdge::Requires(_) => continue,
                    ConflictEdge::Conflict(conflict) => conflict,
                };

                // The only possible conflict at the root level is a Locked conflict
                match conflict {
                    &ConflictCause::Constrains(version_set_id) => {
                        lines.push(format!(
                            "the constraint {name} {version_set} cannot be fulfilled",
                            name = self
                                .interner
                                .display_name(self.interner.version_set_name(version_set_id)),
                            version_set = self.interner.display_version_set(version_set_id),
                        ));
                    }
                    &ConflictCause::ForbidMultipleInstances => {
                        unreachable!()
                    }
                    &ConflictCause::Locked(solvable_id) => {
                        if !reported_locked.insert(solvable_id) {
                            continue;
                        }
                        // A locked solvable that is itself excluded rules the
                        // package out entirely; the reason is part of the
                        // conflict, so report it instead of implying that the
                        // locked version would work.
                        match self.excluded_reason(solvable_id) {
                            Some(reason) => lines.push(format!(
                                "{} is locked, but it is excluded because {}",
                                self.interner.display_merged_solvables(&[solvable_id]),
                                self.interner.display_string(reason),
                            )),
                            None => lines.push(format!(
                                "{} is locked, but another version is required as reported above",
                                self.interner.display_merged_solvables(&[solvable_id]),
                            )),
                        }
                    }
                    ConflictCause::Excluded => continue,
                };
            }

            let indenter = Indenter::new(true);
            let mut lines = lines.into_iter().peekable();
            while let Some(line) = lines.next() {
                let indenter = indenter.push_level_with_order(match lines.peek() {
                    Some(_) => ChildOrder::HasRemainingSiblings,
                    None => ChildOrder::Last,
                });
                writeln!(f, "{}{line}", indenter.get_indent())?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_labels_continue_past_the_alphabet() {
        assert_eq!(label_for(0), "A");
        assert_eq!(label_for(25), "Z");
        assert_eq!(label_for(26), "AA");
        assert_eq!(label_for(27), "AB");
        assert_eq!(label_for(51), "AZ");
        assert_eq!(label_for(52), "BA");
        assert_eq!(label_for(701), "ZZ");
        assert_eq!(label_for(702), "AAA");
    }

    #[test]
    fn test_indenter_without_top_level_indent() {
        let indenter = Indenter::new(false);

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "");

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "└─ ");
    }

    #[test]
    fn test_indenter_with_multiple_siblings() {
        let indenter = Indenter::new(true);

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "└─ ");

        let indenter = indenter.push_level_with_order(ChildOrder::HasRemainingSiblings);
        assert_eq!(indenter.get_indent(), "   ├─ ");

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "   │  └─ ");

        let indenter = indenter.push_level_with_order(ChildOrder::Last);
        assert_eq!(indenter.get_indent(), "   │     └─ ");

        let indenter = indenter.push_level_with_order(ChildOrder::HasRemainingSiblings);
        assert_eq!(indenter.get_indent(), "   │        ├─ ");
    }
}
