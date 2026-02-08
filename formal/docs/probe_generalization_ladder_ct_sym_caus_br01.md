# Probe Generalization Ladder (CT/SYM/CAUS/BR-01)

Purpose: prevent probe-relative locks from becoming an open-ended loophole by pinning
an explicit A/B/C expansion ladder and promotion criteria.

Status: design-only governance artifact (no epistemic status upgrade).

## Scope

- `CT-01` linearization/closure constraints
- `SYM-01` phase symmetry constraints
- `CAUS-01` time-order/causality constraints
- `BR-01` DR-01 to metric bridge outputs used for candidate pruning

## Ladder

### Set A (current baseline)

- Existing pinned baseline probes and locks remain authoritative.
- Required checks:
  - Determinism lock green.
  - Front-door-only import/enforcement lock green.
  - No policy override required.

### Set B (stress probes)

- Add one harder probe family per lane:
  - `CT-01`: widened perturbation and boundary perturbation scans.
  - `SYM-01`: nontrivial phase-path perturbation and conjugation stress case.
  - `CAUS-01`: stricter ordering perturbations and delayed-response edge case.
  - `BR-01`: mixed-shape DR artifacts and fit-method diversity check.
- Promotion gate (`A -> B`):
  - all Set A locks remain green;
  - new Set B locks green under the same disabled-by-default gate policy.

### Set C (cross-domain probes)

- Add cross-domain probe surfaces with explicit comparability declarations.
- Promotion gate (`B -> C`):
  - Set B remains green;
  - cross-domain comparability audit lock green;
  - candidate pruning reason codes remain deterministic and complete.

## Acceptance Contract (per promotion)

- No silent gate enablement.
- No raw/non-artifact bridge inputs.
- No schema drift in locked front-door artifacts.
- Any failure blocks promotion and must be recorded as a bounded failure report.
