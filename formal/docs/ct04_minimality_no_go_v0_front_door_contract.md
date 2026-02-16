# CT-04 Minimality No-Go v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CT-04 minimality/no-go reports.

## Statement (bounded internal)
Under the pinned CT-02/CT-03 energy + causality update bounds, removing the CFL admissibility constraint (cfl_max) yields a detectable violation under the pinned grid/time-step regime and boundary conditions.

## Inputs
- Pinned parameters: length, nx, c_wave, dt_pos, dt_neg, steps_pos, steps_neg, cfl_max.
- Tolerance profile (pinned by default): eps_drift, eps_break.
- Constraint toggle: cfl_bound (positive control) vs cfl_removed (negative control).

## Outputs
- JSON artifacts:
  - `formal/external_evidence/ct04_minimality_no_go_domain_01/ct04_reference_report.json`
  - `formal/external_evidence/ct04_minimality_no_go_domain_01/ct04_candidate_report.json`

## Report schema
`CT-04/minimality_no_go_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: length, nx, dx, c_wave, dt_pos, dt_neg, steps_pos, steps_neg, cfl_max, eps_drift, eps_break.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control).
  - `constraint_mode`, `dt`, `steps`, `cfl`, `rel_drift`, `max_rel_drift`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned parameters and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.ct04_minimality_no_go_front_door
```
