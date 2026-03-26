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

enum Event { StartRootEvt, DescendEvt, FinishEvt, StutterEvt }
one sig Trace {
  var event: one Event,
  var acted_on: one Node
}

// --- Transitions (acyclic only, no SCC yet) ---

// Start a new DFS root: pick any Fresh node when the stack is empty.
pred startRoot[n: Node] {
  // Guards
  CalcStack.depth = 0
  n.gstate = Fresh
  // Effects
  gstate' = gstate ++ (n -> InProgress)
  pushStack[n]
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
  Trace.event' = FinishEvt
  Trace.acted_on' = stackTop
}

pred stutter {
  gstateUnchanged
  stackUnchanged
  Trace.event' = StutterEvt
  Trace.acted_on' = Trace.acted_on
}

fact Transitions {
  always {
    (some n: Node | startRoot[n])
    or (some dep: Node | descend[dep])
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

// --- Exploration commands ---

// Show a trace where some node finishes.
run show {
  eventually some n: Node | n.gstate = Done
} for exactly 4 Node, 5 Int, 10 steps

check StackConsistent {
  always stackConsistent
} for exactly 4 Node, 5 Int, 10 steps

check StackIsInProgress {
  always stackIsInProgress
} for exactly 4 Node, 5 Int, 10 steps

check DepsBeforeDone {
  always depsBeforeDone
} for exactly 4 Node, 5 Int, 10 steps

