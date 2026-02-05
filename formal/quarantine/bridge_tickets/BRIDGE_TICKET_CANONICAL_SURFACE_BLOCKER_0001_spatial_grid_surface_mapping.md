# BRIDGE_TICKET_CANONICAL_SURFACE_BLOCKER_0001 -- Spatial-grid surface mapping for phase/current/pair observables [DESIGN-ONLY]

Status: Design-only (no implementation)

Opened: 2026-02-05

## Purpose (bounded)

Resolve the dominant canonical-surface diversification blocker identified by the feasibility scan:

- `blocked_reason = NO_OBSERVABLE_MAPPING_PHASE_CURRENT_PAIR`
- scanner-native: `reason_code = BLOCKED_NO_SPATIAL_GRID_SURFACE`

This ticket defines (a) the minimal interface a candidate surface must expose to support phase/current/pair mapping, and (b) design-only options to obtain that interface for C7/MT-01a and UCFF candidates.

No runtime bridge computation logic changes are permitted in this ticket.

## Triggering evidence (pinned)

- Scan ticket:
  - `formal/quarantine/bridge_tickets/BRIDGE_TICKET_CANONICAL_SURFACE_SCAN_0001.md`
- Feasibility artifact:
  - `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json`
  - `sha256=36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0`

Pinned scan outcomes:
- C6: `found=true`
- C7/MT-01a: `found=false`, `reason_code=BLOCKED_NO_SPATIAL_GRID_SURFACE`
- UCFF: `found=false`, `reason_code=BLOCKED_NO_SPATIAL_GRID_SURFACE`

## Problem statement (design-only)

Bridge-program comparators for Toy-H/ToyHG require a spatial grid surface (or equivalent typed structure) so the following observables can be computed deterministically:

- phase-related invariance / anchor (Toy-H)
- current-related invariance / anchor (Toy-H)
- pair compatibility (ToyHG pair bridge) which consumes phase/current-like comparators

C7/MT-01a and UCFF candidates are currently not "surface-shaped" in a way that supports these observables, so feasibility fails before any bridge comparison can be attempted.

## Minimal surface interface (mapping contract)

A candidate canonical surface is "grid-surface mappable" iff it can provide:

### Inputs (pinned-compatible)
- `theta: float` (global phase action parameter)
- `grid_n: int` (or an equivalent discretization size)
- `amplitude_scale: float`
- (optional) `local_phase_shear_alpha: float` if the surface supports comparable local deformation tests

### Outputs (required)
At minimum, one of these two output forms must be available:

**Form A -- complex field on a 2D grid**
- `phi: ndarray[complex]` with a deterministic grid layout and deterministic generation for identical inputs

**Form B -- deterministic RHS/operator evaluation on a grid**
- `rhs(phi): ndarray[complex]` or an equivalent canonical operator surface that supports equivariance checks

Additionally required metadata:
- grid geometry description sufficient to compute norms/energies/currents deterministically (or a canonical norm+energy+current evaluator supplied by the surface)

## Mapping objective (what "found=true" would mean)

For C7/MT-01a or UCFF:
- A deterministic surface adapter exists that produces Form A or Form B outputs above
- Adapter admits the existing 17 probe IDs without schema changes
- Observables required by phase/current/pair mapping can be evaluated

This ticket does not implement adapters; it only defines and pins requirements and proposes bounded options.

## Candidate design-only options (bounded)

### Option D1 -- Surface adapter specification (preferred)
Write a design spec for a `SurfaceAdapter` for C7/MT-01a and/or UCFF:
- exact function signature
- determinism requirements
- input coercions (grid sizes, theta handling)
- output shape + dtype requirements

### Option D2 -- Identify existing "hidden" grid surface
If C7/MT-01a or UCFF already contains a grid-level representation somewhere in the repo:
- pin the file path and the function(s) that produce it
- specify how it could be wrapped without changing logic

### Option D3 -- Declare irreducible mismatch (design-only)
If no grid surface exists and creating one would be equivalent to adding a new canonical family:
- mark as design-blocked with `NO_GRID_SURFACE_EXISTS`
- recommend pivot: diversify via a different canonical family that is already grid-shaped

## Deliverables

1. Pinned minimal interface contract (this ticket).
2. For each candidate (C7/MT-01a, UCFF):
   - `adapter_possible: true/false`
   - `blocked_reason` if false (deterministic)
   - pinned evidence (paths/identifiers) supporting the conclusion.
3. Next-ticket recommendation:
   - If any `adapter_possible=true`: mint one implementation ticket to add a surface adapter (scoped to one candidate).
   - If all false: mint one design ticket for alternative diversification target.

## Acceptance criteria

- Fully evidence-bound to the pinned feasibility artifact.
- No runtime bridge logic changes.
- Outputs a deterministic next-ticket recommendation.

## D2 execution log (2026-02-05)

Queries run (repo root):
- `rg -n "C7\b|MT-01a|MT01a|UCFF\b|canonical surface|surface adapter|grid surface|spatial grid" formal`
- `rg -n "Grid2D|Grid|Nx=|Ny=|Lx=|Ly=|dx|dy|ndarray|np\.ndarray|dtype=complex|complex\]" formal/python`
- `rg -n "\bphi\b|rhs_|operator|laplacian|gradient|current|energy|norm" formal/python`
- `rg -n "canonical.*(C7|MT-01a|UCFF)|surface.*(C7|MT-01a|UCFF)" formal/python`
- `rg -n "registry|family|surface_id|canonical_id|report_id.*CANONICAL|feasibility" formal/python/tools`

Targeted absence checks:
- `rg -n "Grid2D|grid_n|theta|local_phase_shear_alpha|\bphi\b|rhs|complex" formal/python/crft/acoustic_metric.py` -> `NO_HITS_C7_MAPPING_TOKENS`
- `rg -n "Grid2D|grid_n|theta|local_phase_shear_alpha|\bphi\b|rhs|complex" formal/python/toe/ucff/core_front_door.py` -> `NO_HITS_UCFF_MAPPING_TOKENS`

## D2 evidence -- C7 / MT-01a (grid surface discovery)

adapter_possible: false
blocked_reason: NO_GRID_SURFACE_EXISTS
scanner_reason_code: BLOCKED_NO_SPATIAL_GRID_SURFACE

Pinned evidence:
- file: `formal/python/crft/acoustic_metric.py`
- symbols:
  - `AcousticMetric2D`
  - `compute_acoustic_metric_1d(rho, u, g_eff)`
  - `compute_acoustic_metric_2d(rho, u_x, u_y, g_eff)`
  - `metric_determinant_2d(metric)`
- output shape: deterministic metric-component arrays (`g_tt`, `g_tx`, `g_ty`, `g_xx`, `g_yy`, `c_s2`) from pre-supplied hydrodynamic arrays; no Form A complex field and no Form B operator/RHS interface.
- mapping-token absence query returned no hits for `Grid2D`, `grid_n`, `theta`, `local_phase_shear_alpha`, `phi`, `rhs`, `complex`.
- canonical-front-door uniqueness lock:
  - `formal/python/tests/test_no_duplicate_acoustic_metric_surface.py` (single MT-01a Python surface at `formal/python/crft/acoustic_metric.py`)

Conclusion:
- No hidden non-archive C7 grid-surface producer was found that satisfies Form A/Form B mapping requirements.

## D2 evidence -- UCFF (grid surface discovery)

adapter_possible: false
blocked_reason: NO_GRID_SURFACE_EXISTS
scanner_reason_code: BLOCKED_NO_SPATIAL_GRID_SURFACE

Pinned evidence:
- UCFF Python surface inventory:
  - `formal/python/toe/ucff/__init__.py`
  - `formal/python/toe/ucff/core_front_door.py`
- file: `formal/python/toe/ucff/core_front_door.py`
- symbols:
  - `UcffCoreInput` (`k: List[float]`)
  - `ucff_dispersion_omega2_numeric(k, params)`
  - `ucff_core_report(inp)` -> report with `k: List[float]`, `omega2: List[float]`
- contract doc:
  - `formal/docs/ucff_core_front_door_contract.md` (1D `k` list in, `omega2` list out; deterministic report surface)
- mapping-token absence query returned no hits for `Grid2D`, `grid_n`, `theta`, `local_phase_shear_alpha`, `phi`, `rhs`, `complex`.

Conclusion:
- No hidden non-archive UCFF grid field or operator surface was found that can be wrapped into Form A/Form B for phase/current/pair bridge mapping.

## D2 outcome summary

| candidate | adapter_possible | blocked_reason | scanner_reason_code |
| --- | --- | --- | --- |
| C7 / MT-01a | false | NO_GRID_SURFACE_EXISTS | BLOCKED_NO_SPATIAL_GRID_SURFACE |
| UCFF | false | NO_GRID_SURFACE_EXISTS | BLOCKED_NO_SPATIAL_GRID_SURFACE |

## Deterministic next-ticket recommendation

All D2 candidates are blocked (`adapter_possible=false` for C7/MT-01a and UCFF). Do not mint an implementation adapter ticket.

Mint a follow-on design ticket for alternative diversification target discovery, scoped to canonical families that are already grid-shaped under existing non-archive front doors.
