# Dynamic Graph Tooling

This folder generates a raw dynamic graph module from Alloy traces.
`pyrefly_fixpoint/v0/PyreflyFixpoint.tla` should not import that raw module
directly; it imports `v0/DynamicGraph.tla`, which wraps the raw graph and
exposes stable helper operators.

## Modules

- Generated `v0/RawDynamicGraph.tla`: defines `Nodes`, `StepCount`,
  `FullGraph`, `DynamicSteps`.
- Stable wrapper `v0/DynamicGraph.tla`: extends `RawDynamicGraph` and defines
  `PushCountInit`, `RecordPush(push_count, n)`, `StepFor(push_count, n)`,
  `Deps(push_count, n)`, `DynamicDeps(push_count, n)`.

## Workflow

1. Generate Alloy traces into `.traces`:
   `alloy6 exec -f -o .traces -t json -r 20 dynamic_graph_gen.als`
2. Convert one trace into a raw TLA module in `.generated`:
   `python3 scripts/alloy_trace_to_tla_constants.py .traces/run$1-solution-10.json .generated/RawDynamicGraph.case0.tla`
3. Install the generated raw module in `v0`:
   `cp .generated/RawDynamicGraph.case0.tla ../v0/RawDynamicGraph.tla`
4. Run TLC from `v0`:
   `tlc -cleanup -metadir states/run-main-$RANDOM -config PyreflyFixpoint.cfg PyreflyFixpoint.tla`

## Example Trace Input

Raw Alloy trace snippet (`.traces/run$1-solution-10.json`):

```json
{
  "instances": [
    {
      "values": {
        "FullGraph$0": {
          "edges": [
            ["Node$0", "Node$0"],
            ["Node$0", "Node$2"],
            ["Node$1", "Node$0"],
            ["Node$1", "Node$1"],
            ["Node$2", "Node$1"]
          ]
        },
        "Params$0": { "step_count": [["4"]] }
      }
    }
  ]
}
```

## Example Generated Output

Generated module (`.generated/RawDynamicGraph.case0.tla`):

```tla
---- MODULE RawDynamicGraph ----

\* Node mapping (alias -> Alloy atom):
\* n0 = Node$0
\* n1 = Node$1
\* n2 = Node$2
\* n3 = Node$3

Nodes == {"n0", "n1", "n2", "n3"}

StepCount == 4

FullGraph ==
[n \in Nodes |->
    IF n = "n0" THEN {"n0", "n2"}
    ELSE IF n = "n1" THEN {"n0", "n1"}
    ELSE IF n = "n2" THEN {"n1"}
    ELSE {}
]

Step0 ==
[n \in Nodes |->
    IF n = "n0" THEN {"n2"}
    ELSE IF n = "n1" THEN {"n0", "n1"}
    ELSE IF n = "n2" THEN {"n1"}
    ELSE {}
]

DynamicSteps ==
    <<Step0, Step1, Step2, Step3>>

====
```

## Contract Targets

- Full-graph cycle set is non-empty.
- Initial step cycle participants match full-graph cycle participants.
- Every `Step[k][n]` is a subset of `FullGraph[n]`.
- Every full edge appears in at least one step (within `StepCount`).
