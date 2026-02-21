# Derivation Target: QFT Gauge Micro-01 Group/Action Surface v0

Spec ID:
- `DERIVATION_TARGET_QFT_GAUGE_MICRO_01_GROUP_ACTION_SURFACE_v0`

Target ID:
- `TARGET-QFT-GAUGE-MICRO-01-GROUP-ACTION-SURFACE-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-001 group/action surface deliverables for the QFT gauge lane.
- Pin typed group and action placeholder surfaces before any quantization or dynamics closure claims.
- Keep the lane bounded, non-claim, and scaffold-only by construction.

Adjudication token:
- `QFT_GAUGE_MICRO01_GROUP_ACTION_ADJUDICATION: NOT_YET_DISCHARGED`

Scope-boundary token:
- `QFT_GAUGE_MICRO01_SCOPE_BOUNDARY_v0: GROUP_ACTION_SURFACE_ONLY_NONCLAIM`

Progress token:
- `QFT_GAUGE_MICRO01_PROGRESS_v0: GROUP_ACTION_SURFACE_TOKEN_PINNED`

## TARGET section

- Group object surface token:
  - `QFT_GAUGE_MICRO01_GROUP_SURFACE_v0: TYPED_GROUP_OBJECT_PINNED`
- Action placeholder surface token:
  - `QFT_GAUGE_MICRO01_ACTION_PLACEHOLDER_SURFACE_v0: TYPED_ACTION_PLACEHOLDER_PINNED`

## CANONICAL_ROUTE section

- Lean scaffold pointer:
  - `formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean`

## BOUNDED_SCOPE section

- non-claim boundary is explicit and binding for this micro artifact.
- group/action scaffold scope only.
- no quantization claim.
- no dynamics derivation claim.
- no Standard Model recovery claim.
- no external truth claim.

## ADJUDICATION_SYNC section

- Cycle-001 micro adjudication token:
  - `QFT_GAUGE_MICRO01_GROUP_ACTION_ADJUDICATION: NOT_YET_DISCHARGED`
- Cycle-001 micro progress token:
  - `QFT_GAUGE_MICRO01_PROGRESS_v0: GROUP_ACTION_SURFACE_TOKEN_PINNED`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean`
- `formal/python/tests/test_qft_gauge_micro01_group_action_surface_gate.py`
