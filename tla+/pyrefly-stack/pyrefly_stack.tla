---- MODULE pyrefly_stack ----

\* Step 3b': Separate global state from SCC-local state.
\*
\* Global state (modeling Calculation cells): Fresh / InProgress / Done.
\* SCC-local state (modeling Scc.node_state): SccInProgress / SccDone.
\* This separation mirrors the implementation: global state lives in
\* Answers/Calculation, SCC state lives in thread-local Scc structs.
\* Merging only touches SCC records, not global state.

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

\* Look up a node's SCC-local state. The node must be in an SCC.
SccState(n) ==
    LET i == SccOf(n)
    IN  scc_stack[i].node_state[n]

\* ---------------------------------------------------------------
\* Type invariant
\* ---------------------------------------------------------------

\* Global states model Calculation cell status.
GlobalStates == {"Fresh", "InProgress", "Done"}

\* SCC-local states model Scc.node_state.
SccNodeStates == {"SccInProgress", "SccDone"}

TypeOk ==
    /\ state \in [Nodes -> GlobalStates]
    /\ graph \in [Nodes -> SUBSET Nodes]
    /\ stack \in Seq(Nodes)
    \* We check scc_stack structure in SccWellFormed instead,
    \* since TLC can't express dependent record types here.

\* Each SCC record has valid members, anchor_pos, and a node_state
\* function whose domain matches members.
SccWellFormed ==
    \A i \in 1..Len(scc_stack) :
        /\ scc_stack[i].members \subseteq Nodes
        /\ scc_stack[i].members /= {}
        /\ scc_stack[i].anchor_pos \in Nat
        /\ DOMAIN scc_stack[i].node_state = scc_stack[i].members
        /\ \A n \in scc_stack[i].members :
               scc_stack[i].node_state[n] \in SccNodeStates

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

\* Push a new SCC record onto scc_stack from a set of cycle members.
\* All members start as SccInProgress.
\* Defines scc_stack' only.
PushNewScc(cycle_members, anchor) ==
    scc_stack' = <<[members |-> cycle_members,
                    anchor_pos |-> anchor,
                    node_state |-> [n \in cycle_members |-> "SccInProgress"]]>>
                 \o scc_stack

\* The top of the stack has a dependency that is InProgress and on
\* the stack: we've found a cycle. Form a new candidate SCC.
\* Global state stays InProgress; SCC-local state tracks membership.
\*
\* For now, this only handles the simple case (no merging).
DetectCycle(dep) ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
       IN  /\ dep \in graph[top]
           /\ state[dep] = "InProgress"
           /\ dep \in StackSet
           /\ ~InAnyScc(dep)
           /\ LET pos == StackPos(dep)
                  cycle_members == StackSlice(pos)
                  anchor == Len(stack) - pos
              IN  /\ PushNewScc(cycle_members, anchor)
                  /\ UNCHANGED <<state, graph, stack>>

\* The top of the stack has all dependencies done (globally Done,
\* or SccDone in the same SCC): pop it.
\* - If not in an SCC: mark global state Done.
\* - If in an SCC: mark SCC-local state SccDone, global stays InProgress.
Complete ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
           inScc == InAnyScc(top)
           topSccIdx == SccOf(top)
       IN  /\ \A dep \in graph[top] :
                \/ state[dep] = "Done"
                \/ /\ InAnyScc(dep)
                   /\ SccState(dep) = "SccDone"
                   /\ SccOf(dep) = topSccIdx
           /\ IF inScc
              THEN /\ scc_stack' = [scc_stack EXCEPT
                       ![topSccIdx].node_state[top] = "SccDone"]
                   /\ UNCHANGED state
              ELSE /\ state' = [state EXCEPT ![top] = "Done"]
                   /\ UNCHANGED scc_stack
           /\ stack' = Tail(stack)
           /\ UNCHANGED graph

Next ==
    \/ \E n \in Nodes : StartRoot(n)
    \/ \E dep \in Nodes : Descend(dep)
    \/ \E dep \in Nodes : DetectCycle(dep)
    \/ Complete

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ---------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------

\* Everything on the stack is globally InProgress.
StackIsInProgress ==
    \A i \in 1..Len(stack) : state[stack[i]] = "InProgress"

\* A node that is globally Done has all deps globally Done.
DepsBeforeDone ==
    \A n \in Nodes :
        state[n] = "Done" =>
            \A dep \in graph[n] : state[dep] = "Done"

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
