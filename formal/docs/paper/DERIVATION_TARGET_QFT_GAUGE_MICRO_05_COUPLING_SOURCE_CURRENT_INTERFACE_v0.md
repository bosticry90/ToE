# Derivation Target: QFT Gauge Micro-05 Coupling Source Current Interface v0

Spec ID:
- `DERIVATION_TARGET_QFT_GAUGE_MICRO_05_COUPLING_SOURCE_CURRENT_INTERFACE_v0`

Target ID:
- `TARGET-QFT-GAUGE-MICRO-05-COUPLING-SOURCE-CURRENT-INTERFACE-v0`

Classification:
- `P-POLICY`

Purpose:
- Freeze Cycle-005 coupling/source-current interface surface deliverables for the QFT gauge lane.
- Pin a statement-only coupling interface before any dynamics or quantization closure attempts.
- Keep the lane bounded, non-claim, and scaffold-only by construction.

Adjudication token:
- `QFT_GAUGE_MICRO05_COUPLING_ADJUDICATION: NOT_YET_DISCHARGED`

Scope-boundary token:
- `QFT_GAUGE_MICRO05_SCOPE_BOUNDARY_v0: COUPLING_INTERFACE_ONLY_NONCLAIM`

Progress token:
- `QFT_GAUGE_MICRO05_PROGRESS_v0: COUPLING_INTERFACE_TOKEN_PINNED`

Coupling surface token:
- `QFT_GAUGE_MICRO05_COUPLING_SURFACE_v0: CURRENT_SOURCE_INTERFACE_STATEMENT_ONLY`

## TARGET section

- Coupling/source-current interface is pinned as a statement-only scaffold.

## CANONICAL_ROUTE section

- Lean scaffold pointer:
  - `formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean`

## BOUNDED_SCOPE section

- coupling interface scaffold scope only.
- statement-only interface (no dynamics equation, no closure).
- no quantization claim.
- no dynamics derivation claim.
- no Standard Model recovery claim.
- no external truth claim.

## ADJUDICATION_SYNC section

- Cycle-005 micro adjudication token:
  - `QFT_GAUGE_MICRO05_COUPLING_ADJUDICATION: NOT_YET_DISCHARGED`
- Cycle-005 micro progress token:
  - `QFT_GAUGE_MICRO05_PROGRESS_v0: COUPLING_INTERFACE_TOKEN_PINNED`

Deliverable pointers:
- `formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md`
- `formal/toe_formal/ToeFormal/QFT/Gauge/ObjectScaffold.lean`
- `formal/python/tests/test_qft_gauge_micro05_coupling_source_current_interface_gate.py`
