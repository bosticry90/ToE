# RL13 Velocity Addition Group-Law v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed RL13 velocity-addition reports for the group-law comparator.

## Inputs
- Pinned parameters: c, beta_u, beta_v.
- Tolerance profile (pinned by default).

## Outputs
- JSON artifacts:
  - `formal/external_evidence/rl13_velocity_addition_group_law_domain_01/rl13_reference_report.json`
  - `formal/external_evidence/rl13_velocity_addition_group_law_domain_01/rl13_candidate_report.json`

## Report schema
`RL/velocity_addition_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: c, beta_u, beta_v, eps_addition, eps_break.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control).
  - `beta_u`, `beta_v`, `beta_comp`, `beta_expected`, `addition_residual`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned parameters and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.rl13_velocity_addition_group_law_front_door
```
