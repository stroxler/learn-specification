# PyreflyFixpoint v1 Design

## Purpose

`PyreflyFixpoint.tla` is a tractable model of Pyrefly's SCC + fixpoint solver.
It focuses on safety properties of SCC discovery, merge/reset behavior, and
phase transitions, while intentionally abstracting away implementation-specific
optimization and concurrency details.

The model now includes dynamic dependency visibility, but dynamicism is provided
as pre-generated static input (from Alloy tooling) rather than generated inside
TLA.

## Scope

This model is intended to answer:

- Do SCC membership-expanding merges force safe restart semantics?
- Do we avoid cross-SCC preliminary-answer leakage?
- Do phase transitions and commit occur only with explicit all-done readiness?
- Under dynamic dependency schedules (with input constraints), do committed SCCs
  still align with truth?

This model is not intended to mirror Rust control flow line-for-line.

## Module Structure

The model is split into three TLA modules:

- `RawDynamicGraph.tla` (generated):
  - Defines `Nodes`, `StepCount`, `FullGraph`, `DynamicSteps`.
- `DynamicGraph.tla` (stable wrapper):
  - Extends `RawDynamicGraph`.
  - Defines helper operators:
    - `PushCountInit`
    - `RecordPush(push_count, n)`
    - `StepFor(push_count, n)`
    - `Deps(push_count, n)` / `DynamicDeps(push_count, n)`
- `PyreflyFixpoint.tla` (solver model):
  - Extends `DynamicGraph` and consumes only wrapper APIs.

This keeps generation concerns separate from solver semantics.

## Dynamic Graph Model

Each node has a per-node push counter (`solve_count` in the spec).
Whenever a node is pushed to the calculation stack, `RecordPush` increments its
counter. The currently visible dependency set is:

- `VisibleGraph(n) == DynamicDeps(solve_count, n)`

`DynamicDeps` uses `StepCount` modulo arithmetic in `DynamicGraph.tla` to map
node push count to one of the pre-generated step graphs in `DynamicSteps`.

So dynamic behavior is modeled as:

- same node, different pushes, potentially different visible deps.

## Phase Model

- `MaxPhase == StepCount - 1`
- Phase `0`: discovery phase.
- Phases `1..MaxPhase`: fixpoint iterations.

Convergence/early-exit is intentionally omitted. The model checks bounded-phase
correctness under fixed iteration budget.

## State Model

Primary variables in `PyreflyFixpoint.tla`:

- `state : [Nodes -> {Fresh, InProgress, Done}]`
- `stack : Seq(Nodes)`
- `scc_stack : Seq(SccRecord)`
- `solve_count : [Nodes -> Nat]`
- `scc_anchors_read : [Nodes -> SUBSET Nat]`

`SccRecord` fields:

- `members`
- `bottom_pos_inclusive`
- `top_pos_exclusive`
- `phase`
- `node_state`
- `prev_answers`
- `curr_answers`

Node-level SCC states:

- `SccFresh`
- `SccInProgress`
- `SccHasPlaceholder`
- `SccDone`

## Stack Convention

The stack now matches Rust `Vec` intuition:

- top is at `stack[Len(stack)]`
- push via `Append(stack, n)`
- pop via `SubSeq(stack, 1, Len(stack)-1)`

This was changed from the previous head-at-index-1 convention to reduce
translation mistakes during implementation review.

## Segment Bookkeeping Model

v1 adds idealized SCC segment algebra over stack positions.

- Each SCC owns a half-open stack segment:
  - `[bottom_pos_inclusive, top_pos_exclusive)`
- `bottom_pos_inclusive` is the segment anchor (deepest cycle frame).
- `top_pos_exclusive` tracks live SCC-participant frames.

Core segment semantics in the model:

- Merge overlap check uses `existing.top_pos_exclusive > cycle_start_pos`.
- Membership-expanding merge sets:
  - `bottom_pos_inclusive = min(overlap bottoms ∪ {cycle_start_pos})`
  - `top_pos_exclusive = Len(stack) + 1`
- SCC participant push increments `top_pos_exclusive`.
- SCC participant pop decrements `top_pos_exclusive`.
- Completion readiness includes `Len(stack) <= bottom_pos_inclusive`
  (anchor frame still present when completion is detected).

## Key Action Semantics

- `StartRoot`: start DFS from a fresh node when stack and SCC stack are empty.
- `Descend`: push a globally fresh dependency visible from current node.
- `DescendIntoSccMember`: during fixpoint phases, push SCC-local fresh member.
- `DetectCycle`: detect back-edge to in-progress node; resolve by
  merge/create/no-op depending on containment.
- `CreatePlaceholder`: cold-path (`phase <= 1`) back-edge handling.
- `ReadPreviousAnswer`: warm-path (`phase >= 2`) back-edge handling.
- `FinishCalculation`: pop stack top and mark done (globally or SCC-local).
- `TransitionPhase`: rotate `curr_answers -> prev_answers`, reset members fresh,
  increment phase.
- `StartNextMember`: choose next fresh SCC member to drive during fixpoint.

Important simplification:

- There is no separate `DemoteScc` action.
- Demotion/reset behavior is subsumed into merge handling (`MergedPhase = 0`
  and cleared answer sets on membership-expanding merge).

## Action-to-Check Matrix

This matrix maps each core action to the primary invariants/properties it is
expected to preserve or enforce.

| Action | Primary checks tied to action |
|---|---|
| `StartRoot` | `TypeOk`, `StackIsInProgress`, `SccWellFormed` |
| `Descend` | `TypeOk`, `StackIsInProgress`, `SccWellFormed` |
| `DescendIntoSccMember` | `TypeOk`, `SccWellFormed`, `SccMembersGloballyInProgress`, `SccMembersDisjoint` |
| `DetectCycle` (no-op contained cycle) | `SccWellFormed`, `SccMembersDisjoint`, `SccSegmentsMonotonicDisjoint` |
| `DetectCycle` (membership-expanding merge) | `MergeExpansionResetsPhase0`, `MergeExpansionClearsAnswers`, `MergeExpansionAbsorbsSegmentFrames`, `PrevAnswersComplete`, `NoCrossSccLeakage` |
| `CreatePlaceholder` | `NoCrossSccLeakage`, `StackIsInProgress` |
| `ReadPreviousAnswer` | `WarmBackedgeNeverUsesPlaceholder`, `PrevAnswersComplete`, `NoCrossSccLeakage` |
| `FinishCalculation` (acyclic node) | `DepsBeforeDone`, `StackIsInProgress` |
| `FinishCalculation` (SCC member) | `SccWellFormed`, `AllAnswersAtCommit`, `CommitOrTransitionRequiresAllDone` |
| `TransitionPhase` | `CommitOrTransitionRequiresAllDone`, `PrevAnswersComplete`, `SccWellFormed` |
| `StartNextMember` | `SccWellFormed`, `StackIsInProgress`, `SccMembersGloballyInProgress` |
| `CommitSccState` | `CommitOrTransitionRequiresAllDone`, `AllAnswersAtCommit`, `CommittedSccMatchesTruth`, `DepsBeforeDone` |

## Safety Checks

### Invariants

Structural:

- `TypeOk`
- `SccWellFormed`
- `StackIsInProgress`
- `DepsBeforeDone`
- `SccMembersGloballyInProgress`
- `SccMembersDisjoint`
- `SccHasLiveMember`
- `SccSegmentRangeIsLive`
- `AtMostOneCompletableScc`
- `SccSegmentsMonotonicDisjoint`
- `SccStackOrdered`

Correctness-oriented:

- `NoCrossSccLeakage`
- `CommittedSccMatchesTruth`
- `PrevAnswersComplete`
- `AllAnswersAtCommit`

### Transition Properties

The model also checks explicit transition-level properties:

- `MergeExpansionResetsPhase0`
- `MergeExpansionClearsAnswers`
- `MergeExpansionAbsorbsSegmentFrames`
- `CommitOrTransitionRequiresAllDone`
- `WarmBackedgeNeverUsesPlaceholder`

These make expected behavior explicit instead of relying on indirect invariant
implications.

## Known Implementation Violations

As of `2026-03-31`, there are known production executions where SCC segment
position bookkeeping can violate the intended live-range contract.

Expected contract (modeled in v1):

- SCC segment ranges are monotonic and disjoint on `scc_stack`.
- Segment bounds always refer to live stack positions for the current execution
  state.

Interpretation:

- These conditions should hold in a correct implementation.
- Current implementation behavior can temporarily violate this contract in some
  traces; this is treated as a bug, not as acceptable behavior.
- The v1 spec keeps these checks enabled as normative safety requirements.

## Dynamic Input Contract Assumptions

The generated dynamic graph cases are constrained to support SCC-discovery
reasoning in this model. In particular, we rely on assumptions equivalent to:

- step graphs are subsets of `FullGraph`
- cycle participants are visible in initial dynamic step
- each full edge appears within the bounded step horizon

These are simulation constraints for model usefulness; they are not claims
about all production executions.

## What v1 Does Not Model (Yet)

### Full Implementation-Shaped Indexing Details

v1 models segment algebra directly, but still intentionally idealizes some
implementation details (for example exact update ordering and saturating math
edge handling). The goal is to specify the algebraic contract clearly rather
than encode every current code-level artifact.

### Concurrency and Calculation-Cell Interleavings

v1 is single-threaded and action-interleaving at the abstract level only.
It does not model concrete multi-thread races around shared `Calculation`
cells, participant promotion, or thread-local/global cycle-detection skew.

Consequence:

- nondeterminism/race bugs discussed in issue docs require either stronger
  abstraction hooks or a dedicated concurrency-aware spec profile.

### Eviction / Degraded-Mode Runtime Behavior

Cross-module eviction and degraded success/no-op paths are not represented.
The model assumes stable context sufficient for SCC/fixpoint reasoning.

## Why Keep v1 Focused

v1 still aims for high signal-to-complexity ratio:

- compact enough for regular TLC runs
- explicit enough for agent reasoning and code review support
- strict enough to catch meaningful SCC/fixpoint contract violations

When we need to validate additional mechanics (concurrency races, eviction
behavior), those should be separate extensions rather than incremental drift
that destabilizes index-algebra validation.
