# Prediction And Falsifier Registry Report v0

Spec ID:
- `PREDICTION_AND_FALSIFIER_REGISTRY_REPORT_v0`

Preparation result:
- `PREDICTION_AND_FALSIFIER_REGISTRY_PREPARED_FROM_MODEL_CARD_TEMPLATE_REVIEW_WITH_NONCLAIM_TEST_DESIGN_CEILINGS`

Authority binding:
- `AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS`
- Consumed result review: `formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0.json`
- Source model-card template: `formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json`
- Source referent registry: `formal/docs/release/REFERENT_REGISTRY_20260515_v0.json`
- Source sensitivity/robustness protocol: `formal/docs/release/SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json`
- Source regime-recovery matrix: `formal/docs/release/REGIME_RECOVERY_MATRIX_20260515_v0.json`
- Source numerical-method registry: `formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json`
- Source VVUQ ledger: `formal/docs/release/VVUQ_CREDIBILITY_LEDGER_20260515_v0.json`
- Source audit: `formal/docs/release/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json`
- JSON registry: `formal/docs/release/PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json`
- Gate: `formal/python/tests/test_prediction_and_falsifier_registry_gate.py`

Non-claim boundary:
- Prediction and falsifier registry only; registers future test designs, observables, pass/fail requirements, dependencies, and claim ceilings without executing predictions, executing falsifiers, upgrading validation, discharging theorem debt, moving blockers, reopening lanes, authorizing Phase 2, claiming empirical validation, closing seams, promoting the master action, or making external-truth claims.

Primary test-design gap:
- `PREDICTION_AND_FALSIFIER_PASS_FAIL_CRITERIA_REGISTERED_BUT_NOT_EXECUTED_V0`

Registry scope:
- `REGISTER_TEST_DESIGNS_ONLY_NO_EXECUTION_OR_RESULT_CLAIM`

## Registry Rows

| Artifact | Applicability | Prediction status | Falsifier status | Quantity | Criteria | Execution | Method debt | UQ | Promotion |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `C6_CP_NLSE_2D_LANE` | `prediction_and_falsifier_relevant` | `candidate_not_executed_v0` | `defined_not_executed_v0` | `dispersion_or_norm_drift_behavior` | `not_fully_registered_v0` | `not_executed_v0` | `method_debt_visible` | `uq_not_quantified` | `false` |
| `C7_MT01A_ACOUSTIC_METRIC_LANE` | `prediction_and_falsifier_relevant` | `candidate_not_executed_v0` | `defined_not_executed_v0` | `acoustic_metric_constraint_or_causal_proxy_behavior` | `not_fully_registered_v0` | `not_executed_v0` | `method_debt_visible` | `uq_not_quantified` | `false` |
| `UCFF_SPECTRAL_AUDIT_LINEAGE` | `structural_falsifier_relevant` | `candidate_not_executed_v0` | `defined_not_executed_v0` | `spectral_structure_or_audit_invariant_behavior` | `not_fully_registered_v0` | `not_executed_v0` | `method_verification_not_applicable_report_surface` | `uq_qualitative` | `false` |
| `BRAGG_DISPERSION_ELIMINATIVE_LANE` | `comparator_falsifier_relevant` | `candidate_not_executed_v0` | `defined_not_executed_v0` | `bragg_dispersion_comparator_residual_behavior` | `not_fully_registered_v0` | `not_executed_v0` | `method_verification_not_applicable_comparator_surface` | `uq_partial_quantitative` | `false` |
| `RL01_RELATIVISTIC_DISPERSION_LIMIT` | `known_limit_falsifier_relevant` | `candidate_not_executed_v0` | `defined_not_executed_v0` | `relativistic_dispersion_limit_behavior` | `not_fully_registered_v0` | `not_executed_v0` | `method_verification_not_applicable_comparator_surface` | `uq_not_quantified` | `false` |
| `RL02_NONRELATIVISTIC_NLSE_LIMIT` | `known_limit_falsifier_relevant` | `candidate_not_executed_v0` | `defined_not_executed_v0` | `nonrelativistic_nlse_limit_behavior` | `not_fully_registered_v0` | `not_executed_v0` | `method_verification_not_applicable_comparator_surface` | `uq_not_quantified` | `false` |
| `GR01_DERIVATION_COMPLETENESS_GATE` | `governance_falsifier_blocked` | `candidate_not_executed_v0` | `defined_not_executed_v0` | `weak_field_or_poisson_derivation_readiness_condition` | `not_fully_registered_v0` | `not_executed_v0` | `method_verification_not_applicable_formal_governance_surface` | `uq_not_quantified` | `false` |
| `BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS` | `seam_mismatch_falsifier_relevant` | `candidate_not_executed_v0` | `defined_not_executed_v0` | `bridge_orthogonality_or_mismatch_witness_behavior` | `not_fully_registered_v0` | `not_executed_v0` | `method_verification_not_applicable_report_surface` | `uq_qualitative` | `false` |

## Summary

- Row count: `8`
- Promotion allowed count: `0`
- Validation upgrade count: `0`
- Prediction execution claim count: `0`
- Falsifier execution claim count: `0`
- Next recommended action: `REVIEW_PREDICTION_AND_FALSIFIER_REGISTRY_RESULT`

Interpretive note:
- This registry records test designs only.
- It does not execute prediction or falsifier checks.
- It does not upgrade validation or authorize physical claim promotion.
