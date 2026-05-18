# Simulation Model Card Template v0

Spec ID:
- `SIMULATION_MODEL_CARD_TEMPLATE_v0`

Preparation result:
- `SIMULATION_MODEL_CARD_TEMPLATE_PREPARED_FROM_REFERENT_REGISTRY_REVIEW_WITH_NONCLAIM_MODEL_DOCUMENTATION_CEILINGS`

Authority binding:
- `AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS`
- Consumed result review: `formal/docs/release/REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json`
- Source referent registry: `formal/docs/release/REFERENT_REGISTRY_20260515_v0.json`
- JSON template: `formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json`
- Gate: `formal/python/tests/test_simulation_model_card_template_gate.py`

Non-claim boundary:
- Simulation model card template only; defines required documentation fields and applicability rules without instantiating model cards, executing simulations, executing comparisons, upgrading validation, discharging theorem debt, moving blockers, reopening lanes, authorizing Phase 2, claiming empirical validation, closing seams, promoting the master action, or making external-truth claims.

Template scope:
- `DEFINE_MODEL_CARD_TEMPLATE_ONLY_NO_CARD_INSTANTIATION_CLAIM`
- Instantiated model card count: `0`
- Promotion allowed default: `false`

## Required Fields

- `model_id`
- `artifact_id`
- `source_path`
- `model_family`
- `purpose`
- `governing_equations_or_report_logic`
- `assumptions`
- `inputs`
- `outputs`
- `numerical_method_or_not_applicable_reason`
- `verification_status`
- `validation_status`
- `known_limit_or_referent_status`
- `uq_status`
- `robustness_status`
- `sensitivity_protocol_status`
- `failure_modes`
- `claim_ceiling`
- `promotion_allowed`
- `forbidden_claims`
- `upgrade_requirements`

## Artifact Class Rules

| Artifact class | Method documentation requirement | Not-applicable reason required |
| --- | --- | --- |
| `simulation_or_numerical_method_surface` | `require_numerical_method_details` | `false` |
| `comparator_or_report_surface` | `require_not_applicable_reason` | `true` |
| `formal_governance_surface` | `require_not_applicable_reason` | `true` |
| `seam_or_mismatch_report_surface` | `require_not_applicable_reason` | `true` |

## Forbidden Claims

- `theorem_discharge`
- `blocker_movement`
- `lane_reopen`
- `phase2_authorization`
- `empirical_validation_claim`
- `seam_closure`
- `master_action_promotion`
- `external_truth_claim`

## Card Skeleton

```yaml
model_id: TEMPLATE_REQUIRED
artifact_id: TEMPLATE_REQUIRED
source_path: TEMPLATE_REQUIRED
model_family: TEMPLATE_REQUIRED
purpose: TEMPLATE_REQUIRED
governing_equations_or_report_logic: TEMPLATE_REQUIRED
assumptions: TEMPLATE_REQUIRED
inputs: TEMPLATE_REQUIRED
outputs: TEMPLATE_REQUIRED
numerical_method_or_not_applicable_reason: TEMPLATE_REQUIRED
verification_status: TEMPLATE_REQUIRED
validation_status: TEMPLATE_REQUIRED
known_limit_or_referent_status: TEMPLATE_REQUIRED
uq_status: TEMPLATE_REQUIRED
robustness_status: TEMPLATE_REQUIRED
sensitivity_protocol_status: TEMPLATE_REQUIRED
failure_modes: TEMPLATE_REQUIRED
claim_ceiling: TEMPLATE_REQUIRED
promotion_allowed: false
forbidden_claims: TEMPLATE_REQUIRED
upgrade_requirements: TEMPLATE_REQUIRED
```

Interpretive note:
- This file is a template only.
- It does not instantiate model cards.
- It does not authorize simulations, comparisons, validation upgrades, or claim promotion.
