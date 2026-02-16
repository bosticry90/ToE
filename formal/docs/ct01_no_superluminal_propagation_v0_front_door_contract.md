# CT-01 No-Superluminal Propagation v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CT-01 propagation reports.

## Statement (bounded internal)
Under the pinned RL05 wave-equation update rule and the pinned RL11 signal-cone admissibility bound, the measured propagation speed of a compact initial disturbance does not exceed the pinned signal-cone speed (within eps_ct01), for the pinned grid/time-step regime and boundary conditions.

## Inputs
- Pinned parameters: length, nx, dt, nt, c_wave, c_cone, amplitude, sigma, x0, delta_x.
- Tolerance profile (pinned by default): eps_ct01, eps_break, u_threshold.
- RL05 and RL11 pinned artifacts are admissible references.

## Outputs
- JSON artifacts:
  - `formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_reference_report.json`
  - `formal/external_evidence/ct01_no_superluminal_propagation_domain_01/ct01_candidate_report.json`

## Report schema
`CT-01/no_superluminal_propagation_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: length, nx, dt, nt, c_wave, c_cone, amplitude, sigma, x0, delta_x, support_radius, u_threshold, eps_ct01, eps_break.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control).
  - `delta_x`, `t_cross`, `v_emp`, `c_cone`, `crossed`, `update_mode`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned parameters and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.ct01_no_superluminal_propagation_front_door
```
