# CT-05 Representation-Invariant Admissibility Class v0 Front Door Contract

Status: Pinned (v0)

This contract defines the deterministic front door that produces typed CT-05 representation-invariant admissibility reports under the pinned CT-02/CT-03 mapping and RL11 signal-cone gate.

## Statement (bounded internal)
Under the pinned RL11 signal-cone admissibility criteria and the pinned CT-02/CT-03 bound functional, admissibility and bound status agree across the representation map within eps for the pinned scenario.

## Inputs
- CT-02 pinned artifacts (reference report).
- CT-03 pinned artifacts (reference report).
- RL11 pinned artifacts (reference report).
- Tolerance profile (pinned by default): eps_rep_invariant, eps_bound_residual.
- Representation break delta (rep_break_delta) for negative control.

## Outputs
- JSON artifacts:
  - `formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01/ct05_reference_report.json`
  - `formal/external_evidence/ct05_rep_invariant_admissibility_class_domain_01/ct05_candidate_report.json`

## Report schema
`CT-05/rep_invariant_admissibility_class_front_door_report/v1`

Fields:
- `schema`, `config_tag`, `regime_tag`, `domain_tag`.
- `params`: eps_rep_invariant, eps_bound_residual, rep_break_delta, ct02_report_fingerprint, ct03_report_fingerprint, rl11_report_fingerprint, ct02_domain_tag, ct03_domain_tag, rl11_domain_tag.
- `boundary`.
- `cases`:
  - `case_id`, `kind` (positive_control | negative_control_rep_break | negative_control_admissibility).
  - `admissible_ref`, `admissible_rep`, `bound_ok_ref`, `bound_ok_rep`, `bound_residual`, `rep_delta`.
- `fingerprint`: sha256 of the report payload (excluding fingerprint).

## Determinism
- The front door is deterministic given pinned inputs and tolerance profile.
- Report fingerprints must match recomputation in the comparator.

## Front door generation
Run:
```
.\py.ps1 -m formal.python.tools.ct05_rep_invariant_admissibility_class_front_door
```
