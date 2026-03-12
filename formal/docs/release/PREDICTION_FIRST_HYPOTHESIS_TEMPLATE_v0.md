# Prediction-First Hypothesis Template v0

Spec ID:
- `PREDICTION_FIRST_HYPOTHESIS_TEMPLATE_v0`

Classification:
- `P-POLICY`

Purpose:
- Standardize hypothesis objects for prediction-first adjudication.
- Bind required fields to protocol-approved retention/prune/inconclusive decisions.

Non-claim boundary:
- template/control artifact only.
- no adjudication by itself.
- no theorem promotion by itself.

Required hypothesis fields
1. `HYPOTHESIS_ID`
2. `MASTER_ACTION_TERM_EMPHASIS`
3. `SEAM_ASSUMPTIONS_USED`
4. `RESIDUAL_OBSERVABLE`
5. `ALTERNATIVE_COMPARATOR`
6. `ELIMINATION_CRITERION`
7. `UNCERTAINTY_WINDOW`
8. `EVIDENCE_TIER`
9. `EXPECTED_DECISION_IF_PASSED`
10. `EXPECTED_DECISION_IF_FAILED`
11. `ARTIFACT_POINTER`
12. `GATE_POINTER`
13. `DECISION_RECORD_POINTER`

Allowed decision tokens
- `RETAIN_v0`
- `PRUNE_v0`
- `INCONCLUSIVE_v0`

Protocol anchors
- `formal/docs/release/FOUNDATIONAL_PREDICTION_SCAFFOLD_PLAN_v0.md`
- `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md`
- `formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md`
