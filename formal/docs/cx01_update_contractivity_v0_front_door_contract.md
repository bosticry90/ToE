# CX-01 Update Contractivity v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CX-01 contractivity reports.

## Statement (bounded internal)
Under the pinned linear update family and pinned l2 norm, a contractive update (`k_contract < 1`) satisfies the admissibility predicate, while an expansive update (`k_break > 1`) is detected as an explicit break by expectation-aware comparator semantics.

## Inputs
- Pinned parameters: state_dim, steps, k_contract, k_break.
- Tolerance profile (pinned by default): eps_contractivity, eps_break.
- Update family: deterministic linear scale map.

## Outputs
- JSON artifacts:
  - `formal/external_evidence/cx01_update_contractivity_domain_01/cx01_reference_report.json`
  - `formal/external_evidence/cx01_update_contractivity_domain_01/cx01_candidate_report.json`

## Report schema
`CX-01/update_contractivity_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: state_dim, steps, k_contract, k_break, eps_contractivity, eps_break.
- `norm_name`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control).
  - `update_mode`, `contraction_factor_per_step`, `steps`, `distance_in`, `distance_out`, `empirical_lipschitz`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned parameters and tolerance profile.
- Report fingerprints must match recomputation in the comparator.
- Active comparator tolerances must match artifact-declared `eps_contractivity` and `eps_break`; mismatches are domain-inconsistent.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.cx01_update_contractivity_front_door
```
