# RL12 Lorentz/Poincare Invariance Proxy v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed RL12 invariance reports for the Lorentz/Poincare proxy comparator.

## Inputs
- Deterministic grid parameters: length, time_window, nx, nt.
- Lorentz boost parameters: c, beta, gamma.
- Boundary tag (string).
- Tolerance profile (pinned by default).

## Outputs
- JSON artifacts:
  - `formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01/rl12_reference_report.json`
  - `formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01/rl12_candidate_report.json`

## Report schema
`RL/lorentz_poincare_invariance_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: length, time_window, nx, nt, dx, dt, c, beta, gamma, eps_invariant, eps_break.
- `boundary`.
- `x`, `t`: grid coordinates.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control).
  - `invariant_metric`: relative L2 difference between base field and Lorentz-boosted field.
  - `u`, `u_boosted`: flattened field values.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned parameters and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.rl12_lorentz_poincare_invariance_proxy_front_door
```
