# Derivation Target: QFT Gauge Micro-03 Curvature Surface v0

Spec ID:
- `DERIVATION_TARGET_QFT_GAUGE_MICRO_03_CURVATURE_SURFACE_v0`

Target ID:
- `TARGET-QFT-GAUGE-MICRO-03-CURVATURE-SURFACE-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-003 curvature-surface deliverables for the QFT gauge lane.
- Pin typed curvature object and relation placeholder surfaces before any closure attempts.
- Keep the lane bounded, non-claim, and scaffold-only by construction.

Adjudication token:
- `QFT_GAUGE_MICRO03_CURVATURE_ADJUDICATION: NOT_YET_DISCHARGED`

Scope-boundary token:
- `QFT_GAUGE_MICRO03_SCOPE_BOUNDARY_v0: CURVATURE_SURFACE_ONLY_NONCLAIM`

Progress token:
- `QFT_GAUGE_MICRO03_PROGRESS_v0: CURVATURE_SURFACE_TOKEN_PINNED`

Curvature surface token:
- `QFT_GAUGE_MICRO03_CURVATURE_SURFACE_v0: F_OBJECT_SURFACE_PINNED`

Curvature relation surface token:
- `QFT_GAUGE_MICRO03_CURVATURE_RELATION_SURFACE_v0: F_EQ_DA_PLUS_A_WEDGE_A_PLACEHOLDER_DECLARED`

## TARGET section

- Curvature object surface `F` is explicitly pinned as a typed scaffold surface.
- Curvature relation surface is explicitly pinned as a placeholder statement surface.

## CANONICAL_ROUTE section

- Lean scaffold pointer:
  - `formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean`

## BOUNDED_SCOPE section

- curvature scaffold scope only.
- placeholder relation only (no proof/closure).
- no dynamics derivation claim.
- no quantization claim.
- no Standard Model recovery claim.
- no external truth claim.

## ADJUDICATION_SYNC section

- Cycle-003 micro adjudication token:
  - `QFT_GAUGE_MICRO03_CURVATURE_ADJUDICATION: NOT_YET_DISCHARGED`
- Cycle-003 micro progress token:
  - `QFT_GAUGE_MICRO03_PROGRESS_v0: CURVATURE_SURFACE_TOKEN_PINNED`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean`
- `formal/python/tests/test_qft_gauge_micro03_curvature_surface_gate.py`
