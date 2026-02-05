# BRIDGE_TICKET_CANONICAL_SURFACE_BLOCKER_0002 -- Phase-action-capable grid surface blocker [DESIGN-ONLY]

Status: Design-only (no implementation)

Opened: 2026-02-05

Branch: `design/canonical-surface-scan`

## Purpose (bounded)

Resolve the dominant actionable non-C6 diversification blocker:

- no phase-action-capable grid surface (Form A/B) exists for non-C6 candidates

This ticket is blocker-analysis only. No runtime/tool logic changes are permitted.

## Triggering evidence (path-pinned)

- `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json`
  - `sha256=36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0`
- `formal/quarantine/feasibility/CRFT_C8_surface_feasibility.json`
  - `sha256=81dc9cd60549861906b02b420c82c0225c794302f40d8d5c6aedf714578236a1`
- `formal/quarantine/bridge_tickets/BRIDGE_TICKET_CANONICAL_SURFACE_DIVERSIFY_0002_grid_shaped_target_discovery.md`
  - commits: `087df14`, `1ea686b`

## Missing capability contract

A candidate is phase-action-capable on a grid iff at least one holds:

- **Form A**: deterministic `phi: ndarray[complex]` on a grid, with pinned global phase action `theta` such that `phi(theta)` is defined.
- **Form B**: deterministic `rhs(phi): ndarray[complex]` (or equivalent operator on a complex grid field), with pinned global phase-action/equivariance checks.

Minimum probe knobs:
- `theta`
- `grid_n`
- `amplitude_scale`
- optional `local_phase_shear_alpha`

## Per-candidate diagnosis

### C7 / MT-01a (grid exists, but no phase action)

- Evidence: `formal/python/crft/acoustic_metric.py`
- Design blocker label: `GRID_EXISTS_BUT_REAL_ONLY_NO_PHASE_ACTION`
- Scanner-native blocker: `BLOCKED_NO_SPATIAL_GRID_SURFACE`
- Resolution options (design-only):
  - R1: define a canonical complex-field surface from which MT-01a is derived
  - R2: define explicit phase-action mapping from a C6-like complex field into metric space (derived-observable lane)
  - R3: declare not bridge-mappable to phase/current/pair and pivot comparator class

### UCFF (no grid surface, 1D dispersion front door only)

- Evidence: `formal/python/toe/ucff/core_front_door.py`
- Contract: `formal/docs/ucff_core_front_door_contract.md`
- Design blocker label: `NO_GRID_SURFACE_EXISTS`
- Scanner-native blocker: `BLOCKED_NO_SPATIAL_GRID_SURFACE`
- Resolution options (design-only):
  - R4: add a new UCFF grid/operator canonical front door
  - R5: formally classify UCFF as non-grid canonical family and route to non-phase/current/pair comparator class

### C8 (secondary blocker; do not dilute primary)

- Evidence: `formal/quarantine/feasibility/CRFT_C8_surface_feasibility.json` (`found=false`)
- Secondary blocker: `UNAVAILABLE_TYPED_FRONT_DOOR`
- Note: tracked for completeness only; primary blocker remains phase-action-capable grid surface availability for non-C6 diversification.

## Blocker summary table

| candidate | grid_exists | phase_action_exists | formA_or_formB | blocker | resolution_choice |
| --- | ---: | ---: | --- | --- | --- |
| C7 / MT-01a | true | false | none | GRID_EXISTS_BUT_REAL_ONLY_NO_PHASE_ACTION | R1 or R2 or R3 |
| UCFF | false | false | none | NO_GRID_SURFACE_EXISTS | R4 or R5 |

## Deterministic next-ticket recommendation rule

Exit by selecting exactly one resolution family:

- If selecting **R1** or **R4** (new surface creation):
  - mint exactly one implementation ticket for one candidate family only
  - scope: typed front door + deterministic artifact generator
  - branch class: implementation (not design-only)
- If selecting **R3** or **R5** (re-scope bridging):
  - mint exactly one design ticket for a new comparator class that does not require phase/current/pair mapping

## Acceptance criteria

- Evidence remains fully path-pinned to the listed artifacts and commits.
- Primary blocker is explicit: phase-action-capable grid surface missing for non-C6 candidates.
- C8 remains secondary and non-diluting.
- Outputs one deterministic next-ticket rule and no runtime changes.
