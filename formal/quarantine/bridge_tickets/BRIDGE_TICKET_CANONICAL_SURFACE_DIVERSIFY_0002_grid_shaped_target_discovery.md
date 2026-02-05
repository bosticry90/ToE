# BRIDGE_TICKET_CANONICAL_SURFACE_DIVERSIFY_0002 -- Alternative grid-shaped canonical target discovery [DESIGN-ONLY]

Status: Design-only (no implementation)

Opened: 2026-02-05

## Purpose (bounded)

Identify one non-C6 canonical family that is already grid-shaped (non-archive, deterministic, typed front door) and therefore a valid next diversification target after C7/MT-01a and UCFF failed D2 adapter discovery.

No runtime bridge logic changes are permitted in this ticket.

## Triggering evidence (pinned)

- `formal/quarantine/bridge_tickets/BRIDGE_TICKET_CANONICAL_SURFACE_BLOCKER_0001_spatial_grid_surface_mapping.md`
  - D2 outcomes: C7/MT-01a `adapter_possible=false`, UCFF `adapter_possible=false`
  - blocker reason: `NO_GRID_SURFACE_EXISTS` (scanner-native `BLOCKED_NO_SPATIAL_GRID_SURFACE`)
- `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json`
  - `sha256=36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0`

## Selection criteria for alternative target

Candidate must satisfy all:
1. Non-archive canonical surface with typed input/output front door.
2. Deterministic behavior for identical pinned inputs.
3. Grid-shaped output or operator surface mappable to:
   - Form A (`phi: ndarray[complex]`) or
   - Form B (`rhs(phi): ndarray[complex]` or equivalent operator surface).
4. Supports existing bridge probe semantics without schema changes, or fails with explicit deterministic blocker.

## Design-only procedure

1. Enumerate candidate canonical families currently present in non-archive Python surfaces.
2. Run or draft deterministic feasibility checks per candidate (documentation/scanner artifacts only).
3. Produce a pinned comparison table (`found=true/false`, blocker reason, artifact path, sha256).
4. Recommend exactly one next implementation ticket if any candidate is feasible.

## D1 inventory evidence (2026-02-05)

Queries executed (repo root):
- `rg -n "Grid2D\.from_box|class Grid2D|from_box\(Nx=" formal/python`
- `rg -n "ndarray\[complex\]|dtype=.*complex|np\.complex|rhs_.*_2d|operator|laplacian|hamiltonian" formal/python`
- `rg -n "core_front_door|FrontDoor|Input\)|Report\)|report_id|contract\.md|typed" formal/python formal/docs`
- `rg -n "\bC[0-9]+\b|canonical|surface_id|canonical_id|MT-" formal/python formal/docs`

Candidate inventory (non-archive canonical front doors):
- C6 control surface:
  - file: `formal/python/crft/cp_nlse_2d.py`
  - symbols: `Grid2D`, `CPParams2D`, `rhs_cp_nlse_2d`, `simulate_cp_nlse_2d`
  - signal: explicit grid class + complex field/RHS surface (Form A/Form B baseline control)
- C7 / MT-01a surface:
  - file: `formal/python/crft/acoustic_metric.py`
  - symbols: `AcousticMetric1D`, `AcousticMetric2D`, `compute_acoustic_metric_2d`, `metric_determinant_2d`
  - signal: deterministic typed arrays from hydrodynamic inputs; no explicit complex field/RHS interface
  - canonical uniqueness lock: `formal/python/tests/test_no_duplicate_acoustic_metric_surface.py`
- UCFF surface:
  - file: `formal/python/toe/ucff/core_front_door.py`
  - symbols: `UcffCoreInput`, `ucff_dispersion_omega2_numeric`, `ucff_core_report`, `dumps_ucff_core_report`
  - signal: deterministic typed 1D `k -> omega2` report surface
  - contract: `formal/docs/ucff_core_front_door_contract.md`
- C8 feasibility-only surface token:
  - scanner: `formal/python/tools/crft_surface_feasibility_scan.py` (token `C8`)
  - artifact: `formal/quarantine/feasibility/CRFT_C8_surface_feasibility.json` (`found=false`)

## D2 feasibility classification (mapping contract)

Deterministic artifact references:
- `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json` (`sha256=36acfd78dafef189877cffa35156abc47d73dd8b80fad3fe1e892ae52f07d7a0`)
- `formal/quarantine/feasibility/CRFT_C8_surface_feasibility.json` (`sha256=81dc9cd60549861906b02b420c82c0225c794302f40d8d5c6aedf714578236a1`)

| candidate | form | found | adapter_possible | blocked_reason | evidence_paths | status |
| --- | --- | --- | --- | --- | --- | --- |
| C6 (control only) | Form A + Form B | true | true | none | `formal/python/crft/cp_nlse_2d.py`; `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json` | complete_control |
| C7 / MT-01a | real metric arrays only (not Form A/B) | false | false | GRID_EXISTS_BUT_REAL_ONLY_NO_PHASE_ACTION | `formal/python/crft/acoustic_metric.py`; `formal/python/tests/test_no_duplicate_acoustic_metric_surface.py`; `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json` | blocked |
| UCFF | 1D report (`k -> omega2`) only (not Form A/B) | false | false | NO_GRID_SURFACE_EXISTS | `formal/python/toe/ucff/core_front_door.py`; `formal/docs/ucff_core_front_door_contract.md`; `formal/quarantine/feasibility/BRIDGE_CANONICAL_SURFACE_SCAN_0001_TOYG_FEASIBILITY.json` | blocked |
| C8 | no canonical non-archive front door found | false | false | UNAVAILABLE_TYPED_FRONT_DOOR | `formal/python/tools/crft_surface_feasibility_scan.py`; `formal/quarantine/feasibility/CRFT_C8_surface_feasibility.json` | blocked |

Scanner-native blocker mapping:
- C7 / MT-01a: `BLOCKED_NO_SPATIAL_GRID_SURFACE`
- UCFF: `BLOCKED_NO_SPATIAL_GRID_SURFACE`
- C8: no canonical front door (`found=false`, prerequisite in artifact)

## D3 recommendation

Non-C6 feasible candidates found: `0`.

Implementation-ticket rule outcome:
- Do not mint an implementation adapter ticket in this cycle.

Next design move:
- Continue blocker-first diversification on missing phase-action/grid-surface capabilities before opening implementation scope.

## Deliverables

1. Pinned candidate inventory for non-C6 canonical families.
2. Deterministic feasibility artifact(s) for each candidate scanned.
3. One recommendation:
   - implementation ticket for a feasible target, or
   - further design blocker ticket if none are feasible.

## Acceptance criteria

- Evidence is deterministic and path-pinned.
- No runtime bridge/tool code changes.
- Recommendation is single-target and implementation-scoped (if feasible).
