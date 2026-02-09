# Comparator Rep Interpretability Manifest Schema v2

Schema ID:
- Toe/comparator_rep_interpretability_manifest/v2

Required top-level keys:
- schema
- policy_token_required_for_cross_rep
- comparators

Allowed rep_interpretability_claim values:
- within_rep_only
- cross_rep_equivalent

Rules:
- within_rep_only entries must not declare proof fields.
- cross_rep_equivalent entries must declare policy_token, proof_artifact, and proof_build_guard_test.
- proof_build_guard_test must build the Lean module inferred from proof_artifact.

Example (within_rep_only):
```json
{
  "module": "formal/python/toe/comparators/cv01_bec_bragg_v0.py",
  "rep_interpretability_claim": "within_rep_only"
}
```

Example (cross_rep_equivalent):
```json
{
  "module": "formal/python/toe/comparators/cv03_ucff_dispersion_v1.py",
  "rep_interpretability_claim": "cross_rep_equivalent",
  "policy_token": "FN_REP_EQ_POLICY_V1",
  "proof_artifact": "formal/toe_formal/ToeFormal/Variational/FNRep32Rep64Equivalence.lean",
  "proof_build_guard_test": "formal/python/tests/test_lean_fn_rep32_rep64_equivalence_build_guard.py"
}
```
