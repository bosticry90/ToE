# Regime Recovery Matrix Report v0

Spec ID:
- `REGIME_RECOVERY_MATRIX_REPORT_v0`

Preparation result:
- `REGIME_RECOVERY_MATRIX_PREPARED_FROM_NUMERICAL_METHOD_REGISTRY_REVIEW_WITH_NONCLAIM_KNOWN_LIMIT_CEILINGS`

Authority binding:
- `AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS`
- Consumed result review: `formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json`
- Source registry: `formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json`
- Source VVUQ ledger: `formal/docs/release/VVUQ_CREDIBILITY_LEDGER_20260515_v0.json`
- Source audit: `formal/docs/release/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json`
- JSON matrix: `formal/docs/release/REGIME_RECOVERY_MATRIX_20260515_v0.json`
- Gate: `formal/python/tests/test_regime_recovery_matrix_gate.py`

Non-claim boundary:
- Regime-recovery matrix only; records known-limit and regime-recovery posture without theorem discharge, blocker movement, lane reopen, Phase 2 authorization, empirical validation claim, seam closure, master-action promotion, recovery completion claim, or external-truth claim.

Primary regime gap:
- `KNOWN_LIMIT_PASS_FAIL_CRITERIA_AND_RECOVERY_EVIDENCE_DEPTH_NOT_COMPLETE_V0`

## Matrix Rows

| Artifact | Applicability | Target regime | Source status | Matrix status | Criterion | Referent | Method dependency | Promotion |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `C6_CP_NLSE_2D_LANE` | `known_limit_recovery_relevant` | `nonlinear_nlse_like_internal_limit` | `partial` | `partial` | `partial` | `analytic_referent_candidate` | `method_debt_visible_convergence_mms_or_solver_crosscheck_unresolved_v0` | `false` |
| `C7_MT01A_ACOUSTIC_METRIC_LANE` | `known_limit_recovery_relevant` | `acoustic_geometry_emergent_metric_limit` | `candidate` | `candidate` | `partial` | `analytic_referent_candidate` | `method_debt_visible_convergence_mms_or_solver_crosscheck_unresolved_v0` | `false` |
| `UCFF_SPECTRAL_AUDIT_LINEAGE` | `regime_comparator_relevant` | `structural_spectral_regime_relevance` | `candidate` | `candidate` | `not_registered_v0` | `not_registered_v0` | `method_verification_not_applicable_report_surface` | `false` |
| `BRAGG_DISPERSION_ELIMINATIVE_LANE` | `regime_comparator_relevant` | `bragg_dispersion_comparator_regime` | `candidate` | `candidate` | `partial` | `empirical_referent_candidate` | `method_verification_not_applicable_comparator_surface` | `false` |
| `RL01_RELATIVISTIC_DISPERSION_LIMIT` | `known_limit_recovery_relevant` | `relativistic_dispersion_limit` | `partial` | `partial` | `partial` | `literature_referent_candidate` | `method_verification_not_applicable_comparator_surface` | `false` |
| `RL02_NONRELATIVISTIC_NLSE_LIMIT` | `known_limit_recovery_relevant` | `nonrelativistic_nlse_limit` | `partial` | `partial` | `partial` | `literature_referent_candidate` | `method_verification_not_applicable_comparator_surface` | `false` |
| `GR01_DERIVATION_COMPLETENESS_GATE` | `formal_governance_blocked` | `weak_field_poisson_gravity_limit` | `blocked` | `blocked` | `blocked` | `blocked` | `method_verification_not_applicable_formal_governance_surface` | `false` |
| `BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS` | `seam_or_mismatch_relevant` | `cross_pillar_seam_mismatch_evidence` | `none` | `not_applicable` | `not_applicable` | `not_applicable` | `method_verification_not_applicable_report_surface` | `false` |

## Summary

- Row count: `8`
- Promotion allowed count: `0`
- Validation upgrade count: `0`
- Recovery completion claim count: `0`
- Next recommended action: `REVIEW_REGIME_RECOVERY_MATRIX_RESULT`

Interpretive note:
- This matrix records known-limit and regime-recovery posture over the existing lineage.
- It does not run new simulations, finish pass/fail criteria, register referents, or upgrade validation.
