# Dynamic Graph Tooling (Scaffold)

This folder is an isolated workspace for generating dynamic graph schedules
from Alloy traces and converting them into copy-pasteable TLA constants.

## Purpose

Separate two concerns:

- Graph/schedule construction (`full_graph`, `dynamic_steps`, etc.)
- Solver correctness checking (TLA/TLC)

The solver spec should consume validated constants; it should not encode graph
construction policy.

## Scope Note

The dynamic-graph constraints in this folder are **simulation assumptions**,
not claims about real-world Pyrefly behavior. They are intentionally stronger
than production behavior so test cases support SCC-discovery-complete
reasoning and stronger invariants in the solver model.

## Primary Workflow

1. Generate traces:
   `alloy6 exec -f -o .traces -t json -r 20 dynamic_graph_gen.als`
2. Convert one solution trace to a TLA constants fragment:
   `python3 scripts/alloy_trace_to_tla_constants.py .traces/run$1-solution-0.json .generated/case0.cfg.inc`
3. Copy constants into a TLC cfg (or include fragment) and run the solver model.

## Example Trace Input

Raw Alloy trace snippet (`.traces/run$1-solution-0.json`):

```json
{
  "instances": [
    {
      "values": {
        "FullGraph$0": {
          "edges": [["Node$0", "Node$2"], ["Node$1", "Node$1"], ["Node$2", "Node$0"]]
        },
        "Params$0": { "step_count": [["4"]] },
        "Step$0": {
          "idx": [["3"]],
          "edges": [["Node$0", "Node$2"], ["Node$2", "Node$0"]]
        },
        "Step$3": {
          "idx": [["0"]],
          "edges": [["Node$0", "Node$2"], ["Node$1", "Node$1"]]
        }
      }
    }
  ]
}
```

## Example `.cfg` Output

Converted TLA constants fragment (`.generated/case0.cfg.inc`):

```tla
\* Node mapping (alias -> Alloy atom):
\* n0 = Node$0
\* n1 = Node$1
\* n2 = Node$2
\* n3 = Node$3
CONSTANT Nodes = {"n0", "n1", "n2", "n3"}
CONSTANT StepCount = 4
CONSTANT FullGraph = [
  "n0" |-> {"n2"},
  "n1" |-> {"n1"},
  "n2" |-> {"n0", "n1", "n2"},
  "n3" |-> {}
]
CONSTANT DynamicSteps = [
  0 |-> [
      "n0" |-> {"n2"},
      "n1" |-> {"n1"},
      "n2" |-> {"n0"},
      "n3" |-> {}
    ],
  1 |-> [
      "n0" |-> {"n2"},
      "n1" |-> {},
      "n2" |-> {"n0", "n1", "n2"},
      "n3" |-> {}
    ],
  2 |-> [
      "n0" |-> {"n2"},
      "n1" |-> {},
      "n2" |-> {"n0", "n1", "n2"},
      "n3" |-> {}
    ],
  3 |-> [
      "n0" |-> {"n2"},
      "n1" |-> {},
      "n2" |-> {"n0", "n1", "n2"},
      "n3" |-> {}
    ]
]
```

## Contract Targets

For each generated case:

- `step_count` defines the dynamic schedule horizon.
- Full-graph cycle set is non-empty (`some FullCycleNodes`).
- Soundness: for each step `k`, `dynamic_steps[k][n] ⊆ full_graph[n]`.
- Initial-cycle alignment: cycle participants in `dynamic_steps[0]`
  exactly match cycle participants in `full_graph`.
- Step-horizon coverage: every edge in `full_graph` appears in at least one step.

These are simulation assumptions used to rule out partial SCC discovery.

## Directory Layout

- `schemas/`: config schema and case schema.
- `dynamic_graph_gen.als`: Alloy generator model for valid graph schedules.
- `scripts/`: trace conversion and optional helpers.
- `.generated/`: output artifacts (ignored except `.gitkeep`).

## Status

Trace generation and conversion are usable now. Schema/validation helpers are
optional guardrails and can be kept lightweight until needed.
