# RL15 Length Contraction Proxy v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed RL15 length-contraction reports for the proxy comparator.

## Inputs
- Pinned parameters: c, beta, gamma, L0.
- Tolerance profile (pinned by default).

## Outputs
- JSON artifacts:
  - `formal/external_evidence/rl15_length_contraction_proxy_domain_01/rl15_reference_report.json`
  - `formal/external_evidence/rl15_length_contraction_proxy_domain_01/rl15_candidate_report.json`

## Report schema
`RL/length_contraction_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: c, beta, gamma, L0, eps_contraction, eps_break.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control).
  - `beta`, `gamma`, `L0`, `L`, `contraction_ratio`, `contraction_residual`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned parameters and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.rl15_length_contraction_proxy_front_door
```
