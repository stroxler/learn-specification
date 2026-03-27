// Pyrefly SCC-solving stack model
// Ported from TLA+ specification

// --- Static structure: dependency graph ---

// Global calculation status for each node.
// Corresponds to state \in [Nodes -> {"Fresh", "InProgress", "Done"}] in TLA+.
enum GlobalState { Fresh, InProgress, Done }

sig Node {
  deps: set Node,
  var gstate: one GlobalState
}

// Limit graph complexity for tractable analysis.
// Each node has at most 3 dependencies (mirrors MaxDeps = 3 in TLA+).
fact BoundDeps {
  all n: Node | #n.deps <= 3
}

// --- SCC state ---

// SCC-local node states, modeling Scc.node_state in the implementation.
enum SccNodeState { SccInProgress, SccHasPlaceholder, SccDone }

// Each Scc atom is a "slot" that can hold an active SCC.
// An SCC is active iff it has members. We pre-allocate enough slots.
sig Scc {
  var members: set Node,
  var anchor: lone Int,
  var nstate: Node -> lone SccNodeState
}

// Active SCCs: those with at least one member.
fun activeSccs: set Scc {
  { s: Scc | some s.members }
}

// Which SCC does node n belong to? At most one, by disjointness.
fun sccOf[n: Node]: lone Scc {
  { s: Scc | n in s.members }
}

// Position of node n on the calc stack (empty if not on stack).
fun stackPos[n: Node]: lone Int {
  CalcStack.elems.n
}

// --- Calc stack (mutable global state) ---

// The calculation stack, modeled as a position-indexed array.
// Position 0 is the bottom; position (depth - 1) is the top.
// Corresponds to `stack \in Seq(Nodes)` in TLA+.
one sig CalcStack {
  var elems: Int -> lone Node,
  var depth: one Int
}

// --- Initial state ---

fact Init {
  // All nodes start Fresh.
  all n: Node | n.gstate = Fresh
  // Stack starts empty.
  CalcStack.depth = 0
  no CalcStack.elems
  // No active SCCs.
  all s: Scc | no s.members and no s.anchor and no s.nstate
  Trace.event = StutterEvt
}

// --- Stack helpers ---

// The node at the top of the stack (empty set if stack is empty).
fun stackTop: lone Node {
  CalcStack.elems[sub[CalcStack.depth, 1]]
}

// The set of all nodes currently on the stack.
// Corresponds to StackSet in TLA+.
fun stackNodes: set Node {
  Int.(CalcStack.elems)
}

// --- Frame conditions ---
// In Alloy 6, we must explicitly say what doesn't change (like UNCHANGED in TLA+).

pred stackUnchanged {
  CalcStack.elems' = CalcStack.elems
  CalcStack.depth' = CalcStack.depth
}

pred gstateUnchanged {
  gstate' = gstate
}

pred sccUnchanged {
  all s: Scc | {
    s.members' = s.members
    s.anchor' = s.anchor
    s.nstate' = s.nstate
  }
}

// --- Stack operations ---

pred pushStack[n: Node] {
  CalcStack.elems' = CalcStack.elems + (CalcStack.depth -> n)
  CalcStack.depth' = add[CalcStack.depth, 1]
}

pred popStack {
  let topIdx = sub[CalcStack.depth, 1] |
    CalcStack.elems' = CalcStack.elems - (topIdx -> stackTop)
  CalcStack.depth' = sub[CalcStack.depth, 1]
}

// --- Event tracking (for trace readability) ---

enum Event { StartRootEvt, DescendEvt, FinishEvt, DetectCycleEvt, StutterEvt }
one sig Trace {
  var event: one Event,
  var acted_on: one Node
}

// --- Transitions ---

// Start a new DFS root: pick any Fresh node when the stack is empty.
pred startRoot[n: Node] {
  // Guards
  CalcStack.depth = 0
  n.gstate = Fresh
  // Effects
  gstate' = gstate ++ (n -> InProgress)
  pushStack[n]
  sccUnchanged
  Trace.event' = StartRootEvt
  Trace.acted_on' = n
}

// The top of the stack has a Fresh dependency: push it.
pred descend[dep: Node] {
  // Guards
  CalcStack.depth > 0
  dep in stackTop.deps
  dep.gstate = Fresh
  // Effects
  gstate' = gstate ++ (dep -> InProgress)
  pushStack[dep]
  sccUnchanged
  Trace.event' = DescendEvt
  Trace.acted_on' = dep
}

// The top of the stack has all deps resolved: pop it and mark Done.
// (Non-SCC version: all deps must be globally Done.)
pred finishCalculation {
  // Guards
  CalcStack.depth > 0
  all dep: stackTop.deps | dep.gstate = Done
  // Effects
  gstate' = gstate ++ (stackTop -> Done)
  popStack
  sccUnchanged
  Trace.event' = FinishEvt
  Trace.acted_on' = stackTop
}

// The top of the stack has an InProgress dependency that is on the stack:
// we've found a back-edge. Create an SCC from the cycle members.
// (Simplified: no merging with existing SCCs yet.)
pred detectCycle[dep: Node] {
  // Guards
  CalcStack.depth > 0
  dep in stackTop.deps
  dep.gstate = InProgress
  dep in stackNodes

  let targetPos = stackPos[dep] |
  let cycleMembers = { n: stackNodes | stackPos[n] >= targetPos } |
  {
    // If cycle is already contained in one SCC, no-op on SCCs
    (some s: activeSccs | cycleMembers in s.members) => {
      sccUnchanged
    } else {
      // Allocate an inactive SCC slot for the new SCC
      some newScc: Scc - activeSccs | {
        newScc.members' = cycleMembers
        newScc.anchor' = targetPos
        newScc.nstate' = cycleMembers -> SccInProgress
        // All other SCCs unchanged
        all s: Scc - newScc | {
          s.members' = s.members
          s.anchor' = s.anchor
          s.nstate' = s.nstate
        }
      }
    }
  }

  gstateUnchanged
  stackUnchanged
  Trace.event' = DetectCycleEvt
  Trace.acted_on' = dep
}

pred stutter {
  gstateUnchanged
  stackUnchanged
  sccUnchanged
  Trace.event' = StutterEvt
  Trace.acted_on' = Trace.acted_on
}

fact Transitions {
  always {
    (some n: Node | startRoot[n])
    or (some dep: Node | descend[dep])
    or (some dep: Node | detectCycle[dep])
    or finishCalculation
    or stutter
  }
}

// --- Invariants ---

// Stack depth matches elements: elems has entries exactly at indices 0..depth-1.
pred stackConsistent {
  all i: Int |
    (i >= 0 and i < CalcStack.depth) iff some CalcStack.elems[i]
}

// Everything on the stack is globally InProgress.
// Corresponds to StackIsInProgress in TLA+.
pred stackIsInProgress {
  all n: stackNodes | n.gstate = InProgress
}

// A node that is Done has all deps Done.
// Corresponds to DepsBeforeDone in TLA+.
pred depsBeforeDone {
  all n: Node |
    n.gstate = Done implies all dep: n.deps | dep.gstate = Done
}

// No node appears in more than one SCC.
// Corresponds to SccMembersDisjoint in TLA+.
pred sccMembersDisjoint {
  all disj s1, s2: activeSccs |
    no (s1.members & s2.members)
}

// SCC members are globally InProgress (never Done while SCC exists).
// Corresponds to SccMembersGloballyInProgress in TLA+.
pred sccMembersInProgress {
  all s: activeSccs | all n: s.members |
    n.gstate = InProgress
}

// Active SCCs have distinct anchors (implicit stack ordering).
// Corresponds to SccStackOrdered in TLA+.
pred sccStackOrdered {
  all disj s1, s2: activeSccs |
    s1.anchor != s2.anchor
}

// Every active SCC has at least one member on the calc stack.
// Corresponds to SccHasLiveMember in TLA+.
pred sccHasLiveMember {
  all s: activeSccs |
    some (s.members & stackNodes)
}

// --- Exploration commands ---

// Show a trace where some node finishes.
// Show a trace where an SCC is formed and visible for at least one state.
// Show a trace where an SCC with 2+ members is formed.
run show {
  some s: Scc | eventually #s.members >= 2
} for exactly 4 Node, exactly 4 Scc, 5 Int, 10 steps

check StackConsistent {
  always stackConsistent
} for exactly 4 Node, 4 Scc, 5 Int, 10 steps

check StackIsInProgress {
  always stackIsInProgress
} for exactly 4 Node, 4 Scc, 5 Int, 10 steps

check DepsBeforeDone {
  always depsBeforeDone
} for exactly 4 Node, 4 Scc, 5 Int, 10 steps

check SccMembersDisjoint {
  always sccMembersDisjoint
} for exactly 4 Node, 4 Scc, 5 Int, 10 steps

check SccMembersInProgress {
  always sccMembersInProgress
} for exactly 4 Node, 4 Scc, 5 Int, 10 steps

check SccStackOrdered {
  always sccStackOrdered
} for exactly 4 Node, 4 Scc, 5 Int, 10 steps

check SccHasLiveMember {
  always sccHasLiveMember
} for exactly 4 Node, 4 Scc, 5 Int, 10 steps

