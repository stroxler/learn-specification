---- MODULE PyreflyFixpoint ----

\* Iterative fixpoint SCC solver with dynamic dependency graphs.
\*
\* This models Pyrefly's SCC solving algorithm where dependency edges
\* are discovered during solving — different phases may traverse
\* different subsets of the true graph. The solver runs a fixed number
\* of iterations (MaxPhase) rather than checking for convergence.
\*
\* Convergence detection is omitted intentionally: in Pyrefly, the
\* iteration count is bounded (e.g., max 5). Convergence is just an
\* optimization that allows early exit when answers stabilize. Since
\* some SCCs genuinely don't converge, the algorithm must be correct
\* without it. This model verifies correctness properties under the
\* fixed-iteration protocol.
\*
\* See DESIGN.md for the full design rationale.

EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS
    Nodes,              \* set of node identifiers
    MaxDeps,            \* max outgoing edges per node (for tractability)
    MaxPhase,           \* number of phases: 0 = discovery, 1..MaxPhase = iterations
    FullTraversalPhase  \* which phase always sees full_graph

\* full_graph and phase_graphs are variables chosen once at Init and
\* then frozen. They are logically constants but TLC's cfg format
\* cannot express function-valued constants, and we want TLC to
\* enumerate possible graphs.
VARIABLES state, stack, scc_stack, full_graph, phase_graphs

vars == <<state, stack, scc_stack, full_graph, phase_graphs>>

\* ---------------------------------------------------------------
\* Assumptions on constants
\* ---------------------------------------------------------------

ASSUME MaxPhase \in Nat
ASSUME FullTraversalPhase \in 0..MaxPhase

\* ---------------------------------------------------------------
\* Helpers
\* ---------------------------------------------------------------

\* The set of all nodes currently on the stack.
StackSet == {stack[i] : i \in 1..Len(stack)}

\* Find the position of node n in the stack (1-indexed from top).
\* Returns 0 if not found.
StackPos(n) ==
    IF \E i \in 1..Len(stack) : stack[i] = n
    THEN CHOOSE i \in 1..Len(stack) : stack[i] = n
    ELSE 0

\* The set of nodes on the stack from position 1 (top) through pos.
StackSlice(pos) ==
    {stack[i] : i \in 1..pos}

\* Which SCC (by index in scc_stack) does node n belong to?
\* Returns 0 if n is not in any SCC.
SccOf(n) ==
    IF \E i \in 1..Len(scc_stack) : n \in scc_stack[i].members
    THEN CHOOSE i \in 1..Len(scc_stack) : n \in scc_stack[i].members
    ELSE 0

\* Is node n in any SCC?
InAnyScc(n) ==
    \E i \in 1..Len(scc_stack) : n \in scc_stack[i].members

\* Look up a node's SCC-local state.
\* Returns "NoScc" if the node is not in any SCC.
SccState(n) ==
    LET i == SccOf(n)
    IN  IF i = 0 THEN "NoScc"
        ELSE scc_stack[i].node_state[n]

\* The phase of the SCC containing node n, or 0 if not in any SCC.
SccPhase(n) ==
    LET i == SccOf(n)
    IN  IF i = 0 THEN 0
        ELSE scc_stack[i].phase

\* The dependency edges visible to node n.
\* Nodes not in any SCC always see full_graph (dynamic visibility
\* only applies within SCC iteration context).
\* Nodes in an SCC see phase_graphs[their SCC's current phase].
VisibleGraph(n) ==
    LET i == SccOf(n)
    IN  IF i = 0
        THEN full_graph[n]
        ELSE phase_graphs[scc_stack[i].phase][n]

\* Minimum / Maximum of a nonempty set of naturals.
MinOfSet(S) == CHOOSE x \in S : \A y \in S : x <= y
MaxOfSet(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Remove entries at indices in `remove` from sequence `seq`.
\* Preserves the relative order of kept entries.
FilterSeq(seq, remove) ==
    LET F[i \in 0..Len(seq)] ==
        IF i = 0 THEN <<>>
        ELSE IF i \in remove THEN F[i-1]
        ELSE Append(F[i-1], seq[i])
    IN F[Len(seq)]

\* ---------------------------------------------------------------
\* Type invariant
\* ---------------------------------------------------------------

\* Global states model Calculation cell status.
GlobalStates == {"Fresh", "InProgress", "Done"}

\* SCC-local node states.
\* SccInProgress: being computed
\* SccHasPlaceholder: a placeholder was created for this node
\*   because another SCC member needed its answer during a
\*   cold phase (0 or 1).
\* SccDone: has a preliminary answer for the current phase.
SccNodeStates == {"SccInProgress", "SccHasPlaceholder", "SccDone"}

TypeOk ==
    /\ state \in [Nodes -> GlobalStates]
    /\ stack \in Seq(Nodes)
    \* scc_stack structure checked in SccWellFormed.

\* Each SCC record has valid members, anchor_pos, phase, and a
\* node_state function whose domain matches members.
SccWellFormed ==
    \A i \in 1..Len(scc_stack) :
        /\ scc_stack[i].members \subseteq Nodes
        /\ scc_stack[i].members /= {}
        /\ scc_stack[i].anchor_pos \in Nat
        /\ scc_stack[i].phase \in 0..MaxPhase
        /\ DOMAIN scc_stack[i].node_state = scc_stack[i].members
        /\ \A n \in scc_stack[i].members :
               scc_stack[i].node_state[n] \in SccNodeStates

\* ---------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------

Init ==
    /\ state = [n \in Nodes |-> "Fresh"]
    /\ stack = <<>>
    /\ scc_stack = <<>>
    \* Choose graphs nondeterministically, subject to constraints.
    /\ full_graph \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes : Cardinality(full_graph[n]) <= MaxDeps
    /\ phase_graphs \in [0..MaxPhase -> [Nodes -> SUBSET Nodes]]
    /\ \A p \in 0..MaxPhase : \A n \in Nodes :
        phase_graphs[p][n] \subseteq full_graph[n]
    /\ \A n \in Nodes :
        phase_graphs[FullTraversalPhase][n] = full_graph[n]

\* ---------------------------------------------------------------
\* SCC merge helpers
\* ---------------------------------------------------------------

\* Indices of existing SCCs that overlap with a set of nodes.
OverlappingSccs(nodes) ==
    {i \in 1..Len(scc_stack) :
        scc_stack[i].members \intersect nodes /= {}}

\* Merge node_states from overlapping SCCs with new cycle members.
\* Existing SCC members keep their current state; new members get
\* SccInProgress.
MergedNodeState(all_members, overlapping) ==
    [n \in all_members |->
        IF \E i \in overlapping : n \in scc_stack[i].members
        THEN LET i == CHOOSE i \in overlapping :
                           n \in scc_stack[i].members
             IN scc_stack[i].node_state[n]
        ELSE "SccInProgress"]

\* Minimum phase across all merged SCCs (new SCCs start at phase 0).
MergedPhase(overlapping) ==
    IF overlapping = {} THEN 0
    ELSE MinOfSet({scc_stack[i].phase : i \in overlapping})

\* For a back-edge to dep, find the relevant stack position.
BackEdgeTargetPos(dep) ==
    LET depSccIdx == SccOf(dep)
    IN  IF depSccIdx /= 0
        THEN LET positions == {StackPos(n) : n \in scc_stack[depSccIdx].members} \ {0}
             IN  IF positions = {} THEN 0
                 ELSE MaxOfSet(positions)
        ELSE StackPos(dep)

\* No-op check: all cycle members are already in a single SCC.
CycleAlreadyContained(cycle_members) ==
    \E i \in 1..Len(scc_stack) :
        cycle_members \subseteq scc_stack[i].members

\* Nontrivial cycle resolution: merge all overlapping SCCs with
\* the new cycle members into a single SCC.
MergeOrCreateScc(cycle_members, anchor) ==
    LET overlapping == OverlappingSccs(cycle_members)
        all_members == cycle_members \union
            UNION {scc_stack[i].members : i \in overlapping}
        all_anchors == {scc_stack[i].anchor_pos : i \in overlapping}
                       \union {anchor}
        min_anchor == MinOfSet(all_anchors)
        merged_phase == MergedPhase(overlapping)
        new_scc == [members    |-> all_members,
                    anchor_pos |-> min_anchor,
                    phase      |-> merged_phase,
                    node_state |-> MergedNodeState(all_members, overlapping)]
        remaining == FilterSeq(scc_stack, overlapping)
    IN scc_stack' = <<new_scc>> \o remaining

ResolveCycle(cycle_members, anchor) ==
    IF CycleAlreadyContained(cycle_members)
    THEN UNCHANGED scc_stack
    ELSE MergeOrCreateScc(cycle_members, anchor)

\* ---------------------------------------------------------------
\* Actions
\* ---------------------------------------------------------------

\* Start a new DFS root: pick any Fresh node when the stack is empty.
StartRoot(n) ==
    /\ stack = <<>>
    /\ state[n] = "Fresh"
    /\ state' = [state EXCEPT ![n] = "InProgress"]
    /\ stack' = <<n>>
    /\ UNCHANGED <<scc_stack, full_graph, phase_graphs>>

\* The top of the stack has a Fresh dependency: push it.
\* Uses VisibleGraph — only edges visible in the current phase
\* can be traversed.
Descend(dep) ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
       IN  /\ dep \in VisibleGraph(top)
           /\ state[dep] = "Fresh"
           /\ state' = [state EXCEPT ![dep] = "InProgress"]
           /\ stack' = <<dep>> \o stack
           /\ UNCHANGED <<scc_stack, full_graph, phase_graphs>>

\* The top of the stack has a dependency that is globally InProgress
\* and either on the stack or in an existing SCC: back-edge found.
\* Uses VisibleGraph for edge visibility.
DetectCycle(dep) ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
       IN  /\ dep \in VisibleGraph(top)
           /\ state[dep] = "InProgress"
           /\ dep \in StackSet \/ InAnyScc(dep)
           /\ LET target_pos == BackEdgeTargetPos(dep)
              IN  /\ target_pos /= 0
                  /\ LET cycle_members == StackSlice(target_pos)
                         anchor == Len(stack) - target_pos
                     IN  /\ ResolveCycle(cycle_members, anchor)
                         /\ UNCHANGED <<state, stack, full_graph, phase_graphs>>

\* The top of the stack is in an SCC and has a dependency that is
\* SccInProgress in the same SCC. A placeholder is created so
\* computation can proceed with a temporary answer.
\* Only valid during cold phases (0 and 1).
CreatePlaceholder(dep) ==
    /\ stack /= <<>>
    /\ scc_stack /= <<>>
    /\ LET top == Head(stack)
           topSccIdx == SccOf(top)
       IN  /\ topSccIdx /= 0
           /\ scc_stack[topSccIdx].phase <= 1
           /\ dep \in VisibleGraph(top)
           /\ SccOf(dep) = topSccIdx
           /\ SccState(dep) = "SccInProgress"
           /\ scc_stack' = [scc_stack EXCEPT
                  ![topSccIdx].node_state[dep] = "SccHasPlaceholder"]
           /\ UNCHANGED <<state, stack, full_graph, phase_graphs>>

\* Is the SCC at index idx fully done and ready to commit?
\* All members must be SccDone and none can be on the calc stack.
SccReadyToCommit(idx, popping_node) ==
    /\ \A n \in scc_stack[idx].members :
        \/ scc_stack[idx].node_state[n] = "SccDone"
        \/ n = popping_node
    /\ \A n \in scc_stack[idx].members :
        \/ n \notin StackSet
        \/ n = popping_node

\* Batch-commit an SCC: all members become globally Done,
\* the SCC is removed from scc_stack.
CommitSccState(idx) ==
    LET scc == scc_stack[idx]
    IN  /\ state' = [n \in Nodes |->
            IF n \in scc.members THEN "Done"
            ELSE state[n]]
        /\ scc_stack' = FilterSeq(scc_stack, {idx})

\* The top of the stack has all dependencies resolved: pop it.
\* A dependency is resolved if it is:
\*   - globally Done (outside any SCC), or
\*   - SccDone or SccHasPlaceholder in the same SCC.
\*
\* Uses VisibleGraph: only visible edges need to be resolved.
\*
\* If not in an SCC: mark global state Done.
\* If in an SCC: mark SCC-local state SccDone. Then, if this was
\*   the last member to finish, batch-commit the entire SCC.
FinishCalculation ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
           topSccIdx == SccOf(top)
       IN  /\ \A dep \in VisibleGraph(top) :
                \/ state[dep] = "Done"
                \/ /\ topSccIdx /= 0
                   /\ SccOf(dep) = topSccIdx
                   /\ SccState(dep) \in {"SccDone", "SccHasPlaceholder"}
           /\ IF topSccIdx = 0
              THEN \* Acyclic node: just mark Done.
                   /\ state' = [state EXCEPT ![top] = "Done"]
                   /\ UNCHANGED scc_stack
              ELSE IF SccReadyToCommit(topSccIdx, top)
              THEN \* Last SCC member to finish: batch-commit.
                   CommitSccState(topSccIdx)
              ELSE \* SCC member but others still in progress:
                   \* just update SCC-local state.
                   /\ scc_stack' = [scc_stack EXCEPT
                        ![topSccIdx].node_state[top] = "SccDone"]
                   /\ UNCHANGED state
           /\ stack' = Tail(stack)
           /\ UNCHANGED <<full_graph, phase_graphs>>

Next ==
    \/ \E n \in Nodes : StartRoot(n)
    \/ \E dep \in Nodes : Descend(dep)
    \/ \E dep \in Nodes : DetectCycle(dep)
    \/ \E dep \in Nodes : CreatePlaceholder(dep)
    \/ FinishCalculation

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ---------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------

\* Everything on the stack is globally InProgress.
StackIsInProgress ==
    \A i \in 1..Len(stack) : state[stack[i]] = "InProgress"

\* A node that is globally Done has all deps (in full_graph) Done.
\* Note: uses full_graph, not VisibleGraph. Once committed, a node's
\* answer must be valid against all real dependencies.
DepsBeforeDone ==
    \A n \in Nodes :
        state[n] = "Done" =>
            \A dep \in full_graph[n] : state[dep] = "Done"

\* SCC members are globally InProgress (never Done while SCC exists).
SccMembersGloballyInProgress ==
    \A i \in 1..Len(scc_stack) :
        \A n \in scc_stack[i].members :
            state[n] = "InProgress"

\* No node appears in more than one SCC.
SccMembersDisjoint ==
    \A i \in 1..Len(scc_stack) :
        \A j \in 1..Len(scc_stack) :
            i /= j => scc_stack[i].members \intersect scc_stack[j].members = {}

\* Every SCC on the scc_stack has at least one member on the calc stack.
SccHasLiveMember ==
    \A i \in 1..Len(scc_stack) :
        \E n \in scc_stack[i].members : n \in StackSet

\* SCCs are ordered on the scc_stack by anchor position.
SccStackOrdered ==
    \A i \in 1..Len(scc_stack) :
        \A j \in 1..Len(scc_stack) :
            i < j => scc_stack[i].anchor_pos >= scc_stack[j].anchor_pos

\* ---------------------------------------------------------------
\* Properties
\* ---------------------------------------------------------------

Finished ==
    \A n \in Nodes : state[n] = "Done"

Liveness == <>Finished

\* ---------------------------------------------------------------
\* Probes
\* ---------------------------------------------------------------

\* "Can a cycle be detected?"
ProbeSccFormed == Len(scc_stack) = 0

====
