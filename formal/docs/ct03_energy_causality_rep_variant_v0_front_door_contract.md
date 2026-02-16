# CT-03 Energy/Causality Representation Variant v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CT-03 energy/causality reports under an alternate representation.

## Statement (bounded internal)
Under the pinned RL07 energy-conserving update rule and the pinned RL11 causality admissibility bound, the energy and CFL constraints remain satisfied under an alternate energy representation (forward-difference energy) for the pinned grid/time-step regime and boundary conditions.

## Inputs
- Pinned parameters: length, nx, c_wave, dt_pos, dt_neg, steps_pos, steps_neg, gamma_negative, cfl_max.
- Tolerance profile (pinned by default): eps_drift, eps_drop, eps_break.
- Representation tag: energy_representation=forward_diff.
- RL07 and RL11 pinned artifacts are admissible references.

## Outputs
- JSON artifacts:
  - `formal/external_evidence/ct03_energy_causality_rep_variant_domain_01/ct03_reference_report.json`
  - `formal/external_evidence/ct03_energy_causality_rep_variant_domain_01/ct03_candidate_report.json`

## Report schema
`CT-03/energy_causality_rep_variant_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: length, nx, dx, c_wave, dt_pos, dt_neg, steps_pos, steps_neg, gamma_negative, cfl_max, eps_drift, eps_drop, eps_break, energy_representation.
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
.\py.ps1 -m formal.python.tools.ct03_energy_causality_rep_variant_front_door
```
