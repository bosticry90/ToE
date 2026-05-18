# Referent Registry Report v0

Spec ID:
- `REFERENT_REGISTRY_REPORT_v0`

Preparation result:
- `REFERENT_REGISTRY_PREPARED_FROM_SENSITIVITY_ROBUSTNESS_REVIEW_WITH_NONCLAIM_REFERENT_CEILINGS`

Authority binding:
- `AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS`
- Consumed result review: `formal/docs/release/SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_20260515_v0.json`
- Source protocol: `formal/docs/release/SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json`
- Source matrix: `formal/docs/release/REGIME_RECOVERY_MATRIX_20260515_v0.json`
- Source registry: `formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json`
- Source VVUQ ledger: `formal/docs/release/VVUQ_CREDIBILITY_LEDGER_20260515_v0.json`
- Source audit: `formal/docs/release/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json`
- JSON registry: `formal/docs/release/REFERENT_REGISTRY_20260515_v0.json`
- Gate: `formal/python/tests/test_referent_registry_gate.py`

Non-claim boundary:
- Referent registry only; registers candidate referent categories, allowed uses, uncertainty gaps, and comparison quantities without executing comparisons, upgrading validation, discharging theorem debt, moving blockers, reopening lanes, authorizing Phase 2, claiming empirical validation, closing seams, promoting the master action, or making external-truth claims.

Primary referent gap:
- `REFERENT_IDENTIFICATION_ALLOWED_USE_AND_UNCERTAINTY_REGISTRATION_INCOMPLETE_V0`

Registry scope:
- `REGISTER_REFERENTS_ONLY_NO_COMPARISON_OR_VALIDATION_EXECUTION_CLAIM`

## Referent Rows

| Artifact | Applicability | Target quantity | Referent type | Allowed use | Comparison | Uncertainty | UQ | Promotion |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `C6_CP_NLSE_2D_LANE` | `simulation_internal_or_analytic_referent_relevant` | `cp_nlse_like_2d_evolution_behavior` | `analytic_or_internal_candidate` | `sanity_check_or_known_limit_context_only` | `not_executed_v0` | `not_registered_v0` | `uq_not_quantified` | `false` |
| `C7_MT01A_ACOUSTIC_METRIC_LANE` | `simulation_internal_or_analytic_referent_relevant` | `acoustic_metric_constraint_behavior` | `analytic_or_internal_candidate` | `sanity_check_context_only` | `not_executed_v0` | `not_registered_v0` | `uq_not_quantified` | `false` |
| `UCFF_SPECTRAL_AUDIT_LINEAGE` | `structural_or_internal_referent_relevant` | `ucff_spectral_structure_and_audit_lineage` | `internal_or_literature_candidate` | `structural_comparator_context_only` | `not_executed_v0` | `not_registered_v0` | `uq_qualitative` | `false` |
| `BRAGG_DISPERSION_ELIMINATIVE_LANE` | `empirical_or_literature_comparator_relevant` | `bragg_dispersion_comparator_behavior` | `empirical_or_literature_candidate` | `benchmark_pressure_or_falsifier_design_only` | `not_executed_v0` | `not_registered_v0` | `uq_partial_quantitative` | `false` |
| `RL01_RELATIVISTIC_DISPERSION_LIMIT` | `known_limit_or_literature_referent_relevant` | `relativistic_dispersion_limit_behavior` | `analytic_or_literature_candidate` | `known_limit_context_only` | `not_executed_v0` | `not_registered_v0` | `uq_not_quantified` | `false` |
| `RL02_NONRELATIVISTIC_NLSE_LIMIT` | `known_limit_or_literature_referent_relevant` | `nonrelativistic_nlse_limit_behavior` | `analytic_or_literature_candidate` | `known_limit_context_only` | `not_executed_v0` | `not_registered_v0` | `uq_not_quantified` | `false` |
| `GR01_DERIVATION_COMPLETENESS_GATE` | `formal_governance_referent_blocked` | `weak_field_or_poisson_governance_requirement` | `analytic_or_formal_requirement_candidate` | `blocker_context_only` | `not_executed_v0` | `not_registered_v0` | `uq_not_quantified` | `false` |
| `BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS` | `seam_or_mismatch_referent_relevant` | `bridge_orthogonality_mismatch_classification` | `internal_report_or_comparator_candidate` | `mismatch_classification_context_only` | `not_executed_v0` | `not_registered_v0` | `uq_qualitative` | `false` |

## Summary

- Row count: `8`
- Promotion allowed count: `0`
- Validation upgrade count: `0`
- Referent comparison execution claim count: `0`
- Empirical validation claim count: `0`
- Next recommended action: `REVIEW_REFERENT_REGISTRY_RESULT`

Interpretive note:
- This registry records candidate referent categories and allowed uses only.
- It does not execute comparisons.
- It does not upgrade validation or authorize physical claim promotion.
