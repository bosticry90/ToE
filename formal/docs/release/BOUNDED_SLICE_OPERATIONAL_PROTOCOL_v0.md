# Bounded Slice Operational Protocol v0

Protocol ID:
- `BOUNDED_SLICE_OPERATIONAL_PROTOCOL_v0`

Status:
- ACTIVE (operational)

Authority posture:
- This protocol is operational and subordinate to repository constitution and existing governance semantics.
- It does not create a new authority layer.

## 1) Purpose

Define one standard bounded-slice workflow that simplifies execution while preserving existing rigor:

- Search -> Referee -> Repair -> Certify
- representation-first triage before hard-slice opening
- bounded file-envelope discipline
- explicit stop conditions
- deterministic closeout and next-lane decision

Non-claim boundary:
- Workflow/governance protocol only.
- No theorem adjudication upgrade by protocol existence.

## 2) Required authority alignment

This protocol must remain aligned with:

1. `New Workflow Constitution.txt`
2. `formal/docs/epistemic_governance_methodology_paper_public_v0.3.md`
3. Existing gate/lock discipline and front-door bridge policy

Hard rule:
- If any instruction in this protocol conflicts with constitutional authority, constitutional authority wins.

## 3) Scope classification

Default use:
- Ordinary bounded science slices (single-lane or tightly local theorem/comparator increments)

Do not use as sole artifact for:
- publication-grade package lock-in
- cross-pillar seam campaigns
- long-lived standards/semantics updates
- locked policy package updates

Exception handling:
- For exception classes, keep dedicated standards/package artifacts separate and link from the slice packet.

## 4) Representation-first pre-slice triage (mandatory)

Before opening a bounded slice, record all fields:

1. Reduced object target:
   - one explicit reduced/compressed object name
2. Blocker class:
   - `ALGEBRAIC` / `SEMANTIC` / `REPRESENTATIONAL` / `MIXED`
3. Alternative exposure path considered:
   - comparator route? symmetry-reduced route? both? none?
4. Ontology-level check:
   - current surface likely right or wrong for objective?
5. Decision:
   - proceed, rescope, or defer

Triage rule:
- Triage informs dispatch only.
- Triage never bypasses admissibility gates.

## 5) Standard bounded-slice lifecycle

### Phase A - Search (route discovery)

Required outputs:
- one-line objective
- candidate route set (at least one preferred route)
- assumptions list
- declared file envelope (required/conditional/disallowed)
- fixed validation ladder draft

Constraints:
- Search artifacts are provisional.
- Search output cannot self-certify.

### Phase B - Referee (critical challenge)

Required outputs:
- explicit objection list
- hidden-dependence checks
- boundary/scope drift checks
- objection dispositions: resolved / unresolved

Constraints:
- unresolved objections are first-class blockers
- if blocker implies envelope widening, stop and rescope

### Phase C - Repair (bounded correction)

Required outputs:
- repair plan linked to objections
- exact edit envelope confirmation
- stop-condition monitor

Constraints:
- no silent widening
- no new gate-family campaign inside ordinary bounded slice
- if broad refactor is needed, stop and issue narrowed rescope

### Phase D - Certify (closure)

Required outputs:
- exact files changed
- exact validations run
- result summary
- unresolved blocker statement
- explicit next-lane decision reason

Constraints:
- certification through Lean/tests/locks only
- no status promotion by prose

## 6) Standard packet schema (default single packet)

Every ordinary bounded slice should use one packet containing these sections:

1. Spec metadata
2. Boundary anchor
3. Objective
4. Bottleneck statement
5. Representation triage block
6. Search outputs
7. Referee objections
8. Repair plan
9. Exact file envelope
10. Fixed validation ladder
11. Stop conditions
12. Acceptance criteria
13. Outcome memo block
14. Next-lane decision gate

Naming recommendation:
- `SLICE_<lane>_<topic>_EXECUTION_PACKET_vN.md`

## 7) Stop conditions (baseline)

Stop immediately and rescope if any occur:

1. File envelope exceeds declared bound
2. Required edits spill into disallowed authority/consumer surfaces
3. New gate family is required for local closure
4. Broad refactor is required outside target chain
5. Control/infrastructure growth exceeds science-core gain

Rescope output requirement:
- Issue narrowed follow-on brief/packet before continuing.

## 8) Validation layers

Each slice must declare three validation layers:

1. Entry validation:
   - packet fields complete and bounded
2. Content validation:
   - theorem/comparator objective evidence succeeded
3. Exit validation:
   - closeout and next-lane decision are protocol-consistent

Execution rule:
- run fixed bounded ladder first
- broader suites only after bounded ladder is green or when explicitly required by phase boundary policy

## 9) Closeout memo discipline

Closeout block is mandatory inside the standard packet and must include:

1. bottleneck addressed
2. exact files changed
3. exact validations run
4. unresolved blocker
5. reason for next lane

## 10) Rollout and anti-regrowth policy

Rollout order:
1. GR01 pilot
2. one statistics/emergence-oriented lane
3. one non-theorem comparator-heavy lane
4. seam/cross-pillar adoption only after pilot success

Anti-regrowth success criterion:
- ordinary slice path must keep manual-authority burden flat or lower than prior multi-artifact baseline.

## 11) Initial pilot mapping (GR01)

Pilot source set for field mapping and equivalence check:

1. `formal/docs/release/SLICE_C_GR01_THEOREM_COMPRESSION_IMPLEMENTATION_BRIEF_v0.md`
2. `formal/docs/release/POST_SLICE_B_EXECUTION_PACKET_v0.md`
3. `formal/docs/release/SLICE_C_GR01_POST_SLICE_MEMO_CYCLE01_v0.md`

Pilot pass condition:
- single-packet form preserves all stop conditions, validation commands, and next-lane decision logic without introducing a second authority surface.

## 12) Related surfaces

Primary checklist alignment:
- `Canonical Verification Checklist.md`

Future automation candidates (not tranche-one):
- `governance_suite.ps1`
- `ARCHITECTURE_SCHEMA_v1.json`

Automation defer rule:
- do not add packet-phase automation until manual pilot passes cleanly.
