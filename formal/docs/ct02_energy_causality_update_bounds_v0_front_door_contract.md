# CT-02 Energy/Causality Update Bounds v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CT-02 energy/causality update reports.

## Statement (bounded internal)
Under the pinned RL07 energy-conserving update rule and the pinned RL11 causality admissibility bound, update families must satisfy both bounded energy drift and the signal-cone CFL bound for the pinned grid/time-step regime and boundary conditions.

## Inputs
- Pinned parameters: length, nx, c_wave, dt_pos, dt_neg, steps_pos, steps_neg, gamma_negative, cfl_max.
- Tolerance profile (pinned by default): eps_drift, eps_drop, eps_break.
- RL07 and RL11 pinned artifacts are admissible references.

## Outputs
- JSON artifacts:
  - `formal/external_evidence/ct02_energy_causality_update_bounds_domain_01/ct02_reference_report.json`
  - `formal/external_evidence/ct02_energy_causality_update_bounds_domain_01/ct02_candidate_report.json`

## Report schema
`CT-02/energy_causality_update_bounds_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: length, nx, dx, c_wave, dt_pos, dt_neg, steps_pos, steps_neg, gamma_negative, cfl_max, eps_drift, eps_drop, eps_break.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control).
  - `gamma`, `dt`, `steps`, `cfl`, `rel_drift`, `rel_drop`, `max_rel_drift`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned parameters and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.ct02_energy_causality_update_bounds_front_door
```
