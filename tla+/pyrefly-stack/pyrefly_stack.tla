---- MODULE pyrefly_stack ----

\* Step 2: DFS traversal of a dependency graph.
\*
\* Nodes have calculation states (Fresh -> InProgress -> Done).
\* A dependency graph is chosen nondeterministically in Init.
\* A stack drives DFS: push fresh dependencies, pop when all deps are done.

EXTENDS Sequences, FiniteSets, Naturals

CONSTANT Nodes

VARIABLES state, graph, stack

vars == <<state, graph, stack>>

\* ---------------------------------------------------------------
\* Type invariant
\* ---------------------------------------------------------------

TypeOk ==
    /\ state \in [Nodes -> {"Fresh", "InProgress", "Done"}]
    /\ graph \in [Nodes -> SUBSET Nodes]
    /\ stack \in Seq(Nodes)

\* ---------------------------------------------------------------
\* Initial state: all Fresh, empty stack, arbitrary acyclic graph
\* with no self-loops. (We'll allow cycles in a later step.)
\* ---------------------------------------------------------------

IsAcyclic(G) ==
    \* No sequence of edges from a node back to itself.
    \* We check this indirectly: in any subset S of Nodes,
    \* if S is nonempty then some member of S has no deps in S.
    \* (This is equivalent to acyclicity for finite graphs.)
    \A S \in SUBSET Nodes :
        S /= {} => \E n \in S : G[n] \intersect S = {}

Init ==
    /\ state = [n \in Nodes |-> "Fresh"]
    /\ graph \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes : n \notin graph[n]       \* no self-loops
    /\ IsAcyclic(graph)
    /\ stack = <<>>

\* ---------------------------------------------------------------
\* Actions
\* ---------------------------------------------------------------

\* Start a new DFS root: pick any Fresh node when the stack is empty.
StartRoot(n) ==
    /\ stack = <<>>
    /\ state[n] = "Fresh"
    /\ state' = [state EXCEPT ![n] = "InProgress"]
    /\ stack' = <<n>>
    /\ UNCHANGED graph

\* The top of the stack has a Fresh dependency: push it.
Descend(dep) ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
       IN  /\ dep \in graph[top]
           /\ state[dep] = "Fresh"
           /\ state' = [state EXCEPT ![dep] = "InProgress"]
           /\ stack' = <<dep>> \o stack
           /\ UNCHANGED graph

\* The top of the stack has all dependencies Done: pop it, mark Done.
Complete ==
    /\ stack /= <<>>
    /\ LET top == Head(stack)
       IN  /\ \A dep \in graph[top] : state[dep] = "Done"
           /\ state' = [state EXCEPT ![top] = "Done"]
           /\ stack' = Tail(stack)
           /\ UNCHANGED graph

Next ==
    \/ \E n \in Nodes : StartRoot(n)
    \/ \E dep \in Nodes : Descend(dep)
    \/ Complete

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ---------------------------------------------------------------
\* Invariants
\* ---------------------------------------------------------------

\* Everything on the stack is InProgress.
StackIsInProgress ==
    \A i \in 1..Len(stack) : state[stack[i]] = "InProgress"

\* No node is Done unless all its dependencies are Done.
DepsBeforeDone ==
    \A n \in Nodes :
        state[n] = "Done" =>
            \A dep \in graph[n] : state[dep] = "Done"

\* ---------------------------------------------------------------
\* Properties
\* ---------------------------------------------------------------

Finished ==
    \A n \in Nodes : state[n] = "Done"

Liveness == <>Finished

\* ---------------------------------------------------------------
\* Probes (temporarily add to INVARIANT in cfg to see traces)
\* ---------------------------------------------------------------

\* "Can the stack ever have 2+ elements?"
\* TLC will show a trace with a real DFS descent.
\* ProbeDeepStack ==
\*    Len(stack) < 2

====
