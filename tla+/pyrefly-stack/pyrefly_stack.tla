---- MODULE pyrefly_stack ----

\* Step 3b: SCC detection (single cycle, no merging yet).
\*
\* Adds scc_stack and new node states (InProgressInScc, DoneInScc).
\* When Descend finds a dependency that's already InProgress on the
\* stack, a candidate SCC is formed from the cycle members.

EXTENDS Sequences, FiniteSets, Naturals

CONSTANT Nodes

VARIABLES state, graph, stack, scc_stack

vars == <<state, graph, stack, scc_stack>>

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
\* These are the nodes in the cycle: from the back-edge target up to
\* the current top of stack.
StackSlice(pos) ==
    {stack[i] : i \in 1..pos}

\* ---------------------------------------------------------------
\* Type invariant
\* ---------------------------------------------------------------

NodeStates == {"Fresh", "InProgress", "InProgressInScc", "DoneInScc", "Done"}

SccRecord == [members : SUBSET Nodes, anchor_pos : Nat]

TypeOk ==
    /\ state \in [Nodes -> NodeStates]
    /\ graph \in [Nodes -> SUBSET Nodes]
    /\ stack \in Seq(Nodes)
    /\ scc_stack \in Seq(SccRecord)

\* ---------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------

Init ==
    /\ state = [n \in Nodes |-> "Fresh"]
    /\ graph \in [Nodes -> SUBSET Nodes]
    /\ stack = <<>>
    /\ scc_stack = <<>>

\* ---------------------------------------------------------------
\* Actions
\* ---------------------------------------------------------------

\* Start a new DFS root: pick any Fresh node when the stack is empty.
StartRoot(n) ==
    /\ stack = <<>>
    /\ state[n] = "Fresh"
    /\ state' = [state EXCEPT ![n] = "InProgress"]
    /\ stack' = <<n>>
    /\ UNCHANGED <<graph, scc_stack>>

\* The top of the stack has a Fresh dependency: push it.
Descend(dep) ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
       IN  /\ dep \in graph[top]
           /\ state[dep] = "Fresh"
           /\ state' = [state EXCEPT ![dep] = "InProgress"]
           /\ stack' = <<dep>> \o stack
           /\ UNCHANGED <<graph, scc_stack>>

\* The top of the stack has a dependency that is InProgress and on
\* the stack: we've found a cycle. Form a new candidate SCC from
\* all nodes between the target and the top of stack (inclusive).
\* All cycle members become InProgressInScc.
\*
\* For now, this only handles the case where no SCC exists yet
\* (no merging). We require the target is plain InProgress.
DetectCycle(dep) ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
       IN  /\ dep \in graph[top]
           /\ state[dep] = "InProgress"
           /\ dep \in StackSet
           /\ LET pos == StackPos(dep)
                  cycle_members == StackSlice(pos)
                  new_state == [n \in Nodes |->
                      IF n \in cycle_members
                      THEN "InProgressInScc"
                      ELSE state[n]]
                  \* anchor_pos is the position from the bottom of
                  \* the stack (convert from top-indexed)
                  anchor == Len(stack) - pos
              IN  /\ scc_stack' = <<[members |-> cycle_members,
                                     anchor_pos |-> anchor]>>
                                  \o scc_stack
                  /\ state' = new_state
                  /\ UNCHANGED <<graph, stack>>

\* The top of the stack has all dependencies either Done or
\* DoneInScc: pop it.
\* - If the node is InProgress (acyclic), mark it Done.
\* - If the node is InProgressInScc, mark it DoneInScc.
Complete ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
       IN  /\ \A dep \in graph[top] :
                state[dep] \in {"Done", "DoneInScc"}
           /\ state' = [state EXCEPT ![top] =
                IF state[top] = "InProgress" THEN "Done"
                ELSE "DoneInScc"]
           /\ stack' = Tail(stack)
           /\ UNCHANGED <<graph, scc_stack>>

Next ==
    \/ \E n \in Nodes : StartRoot(n)
    \/ \E dep \in Nodes : Descend(dep)
    \/ \E dep \in Nodes : DetectCycle(dep)
    \/ Complete

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ---------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------

\* Everything on the stack is in an in-progress state.
StackIsInProgress ==
    \A i \in 1..Len(stack) :
        state[stack[i]] \in {"InProgress", "InProgressInScc"}

\* No node is Done unless all its dependencies are Done.
\* (DoneInScc deps are ok for DoneInScc nodes but not for Done.)
DepsBeforeDone ==
    \A n \in Nodes :
        /\ state[n] = "Done" =>
              \A dep \in graph[n] : state[dep] = "Done"
        /\ state[n] = "DoneInScc" =>
              \A dep \in graph[n] : \/ state[dep] = "Done"
                                    \/ state[dep] = "DoneInScc"
                                    \/ state[dep] = "InProgressInScc"

\* Every SCC member is either in-progress or done-in-scc.
SccMembersConsistent ==
    \A i \in 1..Len(scc_stack) :
        \A n \in scc_stack[i].members :
            state[n] \in {"InProgressInScc", "DoneInScc"}

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
