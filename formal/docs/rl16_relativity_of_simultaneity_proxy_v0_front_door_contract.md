# RL16 Relativity of Simultaneity Proxy v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed RL16 simultaneity-shift reports for the proxy comparator.

## Inputs
- Pinned parameters: c, beta, gamma, delta_t, delta_x.
- Tolerance profile (pinned by default).

## Outputs
- JSON artifacts:
  - `formal/external_evidence/rl16_relativity_of_simultaneity_proxy_domain_01/rl16_reference_report.json`
  - `formal/external_evidence/rl16_relativity_of_simultaneity_proxy_domain_01/rl16_candidate_report.json`

## Report schema
`RL/relativity_of_simultaneity_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: c, beta, gamma, delta_t, delta_x, eps_simultaneity, eps_break.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control).
  - `beta`, `gamma`, `delta_t`, `delta_x`, `delta_t_prime`, `simultaneity_residual`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned parameters and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.rl16_relativity_of_simultaneity_proxy_front_door
```
