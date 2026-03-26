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

// Initially all nodes are Fresh.
fact Init {
  all n: Node | n.gstate = Fresh
}

// --- Exploration commands ---

// Show a small graph instance
run show {} for exactly 4 Node
