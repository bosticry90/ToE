from __future__ import annotations

import copy
import math
from typing import Any


CLASSIFIER_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_CLASSIFIER_v0"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_classifier_v0.py"
)
HYPOTHESES_A_TO_D = [
    "H_A_CANCELLATION_CONDITIONING",
    "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
    "H_C_DISCRETE_CLOSURE_MISMATCH",
    "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
]
H_E = "H_E_UNRESOLVED_MECHANISM"
EXPECTED_RUN_IDS = [
    "MECHv0:R13_LOOSE:INSTRUMENTED",
    "MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL",
    "MECHv0:R13_TIGHT:INSTRUMENTED",
    "MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL",
    "MECHv0:R10_LOOSE:INSTRUMENTED",
    "MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL",
]
EVIDENCE_OUTCOMES = [
    "EVIDENCE_ADMISSIBLE",
    "BLOCKED_CUSTODY",
    "BLOCKED_RUN_IDENTITY",
    "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
    "BLOCKED_INSTRUMENTATION_PERTURBATION",
    "BLOCKED_OBSERVABLE_SEMANTICS",
    "BLOCKED_OPERATOR_BINDING",
]
AGGREGATE_OUTCOMES = [
    "BLOCKED",
    "SINGLE_SUPPORTED_MECHANISM",
    "MULTIPLE_SUPPORTED_MECHANISMS",
    "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE",
]
CLASSIFIER_PRECEDENCE = [
    "verify design, implementation, operator, and separate-output custody",
    "verify exact run and payload identities",
    "verify every mandatory payload is present",
    "verify every mandatory observable is present",
    "verify instrumentation nonperturbation",
    "verify output schemas, units, norms, normalizations, and floors",
    "verify actual discrete-operator binding",
    "evaluate H_A independently",
    "evaluate H_B independently",
    "evaluate H_C independently",
    "evaluate H_D independently",
    "preserve every individual hypothesis decision and criterion record",
    "construct ordered supported_mechanism_ids",
    "assign aggregate mechanism result from support-set cardinality",
    "assign H_E only for complete admissible evidence with an empty support set",
    "apply the numerical-mechanism-only claim ceiling",
]
REQUIRED_GATE_FIELDS = [
    "custody_passed",
    "observed_run_ids",
    "required_payloads_complete",
    "required_observables_complete",
    "separate_output_custody_passed",
    "instrumentation_nonperturbation_passed",
    "observable_semantics_passed",
    "discrete_operator_binding_passed",
]
REQUIRED_METRIC_FIELDS = [
    "exchange_conditioning",
    "block_dominance",
    "discrete_closure",
    "distributed_accumulation",
]
ROLE_KEYS = ["R13_LOOSE", "R13_TIGHT", "R10_LOOSE_NEIGHBOR"]
SUPPORT_CONSTANTS = {
    "H_A": {
        "loose_median_kappa_minimum": 1.0e6,
        "severe_step_fraction_minimum": 0.75,
        "directional_log10_contrast_minimum": 1.0,
        "required_postinitial_step_count": 16,
    },
    "H_B": {
        "eligible_longitudinal_block_ids": [
            "THETA_KINEMATIC",
            "P_LONGITUDINAL_MAXWELL",
        ],
        "dominance_share_minimum": 0.50,
        "dominant_step_fraction_minimum": 0.75,
        "median_share_advantage_minimum": 0.20,
        "median_share_ratio_minimum": 2.0,
    },
    "H_C": {
        "roundoff_bound_gamma_operation_count": 32,
        "roundoff_bound_violation_ratio_strictly_above": 1.0,
        "minimum_consecutive_violation_steps": 2,
        "loose_to_tight_max_ratio_minimum": 10.0,
        "loose_to_neighbor_max_ratio_minimum": 2.0,
        "required_postinitial_step_count": 16,
    },
    "H_D": {
        "minimum_contributing_block_count_per_step": 3,
        "per_block_share_minimum": 0.10,
        "effective_block_count_minimum": 3.0,
        "single_block_share_maximum_exclusive": 0.50,
        "distributed_step_fraction_minimum": 0.75,
        "distributed_fraction_advantage_over_each_reference_minimum": 0.25,
        "linked_structural_series_count": 4,
        "minimum_nondecreasing_increments_per_series": 14,
    },
}
CLAIM_CEILING = (
    "NUMERICAL_MECHANISM_EVIDENCE_ONLY; no robustness reclassification, materiality, "
    "physical instability, model-domain boundary, E-REPRO, pillar, seam, C_k, CCFT, "
    "or master-action promotion"
)


def _criterion(
    criterion_id: str,
    passed: bool,
    observed: Any,
    rule: str,
    evidence_ids: list[str],
) -> dict[str, Any]:
    return {
        "criterion_id": criterion_id,
        "status": "PASSED" if passed else "FAILED",
        "evidence_ids": list(evidence_ids),
        "reason": f"observed={observed!r}; frozen_rule={rule}",
    }


def _decision(
    hypothesis_id: str,
    necessary: list[dict[str, Any]],
    supporting: list[dict[str, Any]],
    evidence_ids: list[str],
) -> dict[str, Any]:
    supported = bool(necessary) and all(item["status"] == "PASSED" for item in necessary)
    reasons = [item["reason"] for item in necessary + supporting]
    return {
        "hypothesis_id": hypothesis_id,
        "status": "SUPPORTED" if supported else "NOT_SUPPORTED",
        "evidence_ids": list(dict.fromkeys(evidence_ids)),
        "necessary_condition_decisions": necessary,
        "supporting_condition_decisions": supporting,
        "decision_reasons": reasons,
    }


def _not_evaluated(hypothesis_id: str, evidence_result: str) -> dict[str, Any]:
    return {
        "hypothesis_id": hypothesis_id,
        "status": "NOT_EVALUATED",
        "evidence_ids": [],
        "necessary_condition_decisions": [],
        "supporting_condition_decisions": [],
        "decision_reasons": [f"suppressed_by={evidence_result}"],
    }


def _blocked(evidence_result: str, diagnostic: str) -> dict[str, Any]:
    return {
        "classifier_id": CLASSIFIER_ID,
        "evidence_result": evidence_result,
        "evidence_diagnostic": diagnostic,
        "hypothesis_decisions": {
            hypothesis_id: _not_evaluated(hypothesis_id, evidence_result)
            for hypothesis_id in HYPOTHESES_A_TO_D + [H_E]
        },
        "supported_mechanism_ids": [],
        "aggregate_mechanism_result": "BLOCKED",
        "claim_ceiling": CLAIM_CEILING,
    }


def _gate(evidence: dict[str, Any]) -> tuple[str, str] | None:
    missing_gate = [field for field in REQUIRED_GATE_FIELDS if field not in evidence]
    if missing_gate:
        return (
            "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
            f"REQUIRED_GATE_FIELD_MISSING:{missing_gate[0]}",
        )
    if evidence["custody_passed"] is not True:
        return "BLOCKED_CUSTODY", "CUSTODY_OR_IMPLEMENTATION_IDENTITY_FAILED"
    if evidence["separate_output_custody_passed"] is not True:
        return "BLOCKED_CUSTODY", "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL"
    observed_ids = evidence["observed_run_ids"]
    if not isinstance(observed_ids, list):
        return "BLOCKED_RUN_IDENTITY", "EXPECTED_RUN_ID_CLOSURE_MISMATCH"
    if len(set(observed_ids)) != len(observed_ids):
        return "BLOCKED_RUN_IDENTITY", "DUPLICATE_RUN_IDENTITY"
    if observed_ids != EXPECTED_RUN_IDS:
        return "BLOCKED_RUN_IDENTITY", "EXPECTED_RUN_ID_CLOSURE_MISMATCH"
    if evidence["required_payloads_complete"] is not True:
        return "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "REQUIRED_OUTPUT_MISSING"
    if evidence["required_observables_complete"] is not True:
        return "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "REQUIRED_OBSERVABLE_MISSING"
    if evidence["instrumentation_nonperturbation_passed"] is not True:
        return (
            "BLOCKED_INSTRUMENTATION_PERTURBATION",
            "INSTRUMENTED_TRAJECTORY_NOT_BYTE_IDENTICAL",
        )
    if evidence["observable_semantics_passed"] is not True:
        return "BLOCKED_OBSERVABLE_SEMANTICS", "OBSERVABLE_UNIT_OR_NORMALIZATION_INVALID"
    if evidence["discrete_operator_binding_passed"] is not True:
        return "BLOCKED_OPERATOR_BINDING", "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED"
    metrics = evidence.get("metrics")
    if not isinstance(metrics, dict):
        return "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "MECHANISM_METRICS_MISSING"
    missing_metrics = [field for field in REQUIRED_METRIC_FIELDS if field not in metrics]
    if missing_metrics:
        return (
            "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
            f"MECHANISM_METRIC_MISSING:{missing_metrics[0]}",
        )
    return None


def _role_metric(metrics: dict[str, Any], family: str, role: str) -> dict[str, Any]:
    value = metrics[family].get(role)
    if not isinstance(value, dict):
        raise ValueError(f"missing {family} metric for {role}")
    return value


def _finite_float(value: Any, field: str) -> float:
    numeric = float(value)
    if not math.isfinite(numeric):
        raise ValueError(f"nonfinite metric {field}")
    return numeric


def _positive_ratio(numerator: float, denominator: float, field: str) -> float:
    if numerator < 0.0 or denominator < 0.0:
        raise ValueError(f"negative ratio operand {field}")
    if denominator == 0.0:
        return math.inf if numerator > 0.0 else 1.0
    return numerator / denominator


def _directional_log10_contrast(loose: float, reference: float, field: str) -> float:
    if loose < 0.0 or reference < 0.0:
        raise ValueError(f"negative log contrast operand {field}")
    # By construction kappa is either zero (no transfer) or at least order one.
    # A floor of one keeps the contrast finite without inventing a sub-unit
    # conditioning distinction.
    value = math.log10(max(loose, 1.0) / max(reference, 1.0))
    if not math.isfinite(value):
        raise ValueError(f"nonfinite log contrast {field}")
    return value


def _evaluate_H_A(metrics: dict[str, Any]) -> dict[str, Any]:
    loose = _role_metric(metrics, "exchange_conditioning", ROLE_KEYS[0])
    tight = _role_metric(metrics, "exchange_conditioning", ROLE_KEYS[1])
    neighbor = _role_metric(metrics, "exchange_conditioning", ROLE_KEYS[2])
    threshold = SUPPORT_CONSTANTS["H_A"]
    evidence_ids = [
        "OBS_EXCHANGE_KAPPA:R13_LOOSE",
        "OBS_EXCHANGE_KAPPA:R13_TIGHT",
        "OBS_EXCHANGE_KAPPA:R10_LOOSE_NEIGHBOR",
    ]
    kappa = _finite_float(loose["median_kappa"], "H_A.loose.median_kappa")
    tight_kappa = _finite_float(tight["median_kappa"], "H_A.tight.median_kappa")
    neighbor_kappa = _finite_float(
        neighbor["median_kappa"], "H_A.neighbor.median_kappa"
    )
    tight_contrast = _directional_log10_contrast(
        kappa, tight_kappa, "H_A.tight_contrast"
    )
    neighbor_contrast = _directional_log10_contrast(
        kappa, neighbor_kappa, "H_A.neighbor_contrast"
    )
    necessary = [
        _criterion(
            "H_A_KAPPA_MATERIAL",
            kappa >= threshold["loose_median_kappa_minimum"],
            kappa,
            f">={threshold['loose_median_kappa_minimum']}",
            evidence_ids,
        ),
        _criterion(
            "H_A_SEVERE_STEP_PERSISTENCE",
            _finite_float(
                loose["severe_step_fraction"], "H_A.loose.severe_step_fraction"
            )
            >= threshold["severe_step_fraction_minimum"],
            loose["severe_step_fraction"],
            f">={threshold['severe_step_fraction_minimum']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_A_COMPLETE_STEP_SERIES",
            int(loose["sample_count"])
            == threshold["required_postinitial_step_count"],
            int(loose["sample_count"]),
            f"=={threshold['required_postinitial_step_count']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_A_TIGHT_DIRECTIONAL_CONTRAST",
            tight_contrast >= threshold["directional_log10_contrast_minimum"],
            tight_contrast,
            f">={threshold['directional_log10_contrast_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_A_NEIGHBOR_DIRECTIONAL_CONTRAST",
            neighbor_contrast >= threshold["directional_log10_contrast_minimum"],
            neighbor_contrast,
            f">={threshold['directional_log10_contrast_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
    ]
    return _decision(HYPOTHESES_A_TO_D[0], necessary, [], evidence_ids)


def _evaluate_H_B(metrics: dict[str, Any]) -> dict[str, Any]:
    loose = _role_metric(metrics, "block_dominance", ROLE_KEYS[0])
    tight = _role_metric(metrics, "block_dominance", ROLE_KEYS[1])
    neighbor = _role_metric(metrics, "block_dominance", ROLE_KEYS[2])
    threshold = SUPPORT_CONSTANTS["H_B"]
    evidence_ids = [
        "OBS_BLOCK_DOMINANCE:R13_LOOSE",
        "OBS_BLOCK_DOMINANCE:R13_TIGHT",
        "OBS_BLOCK_DOMINANCE:R10_LOOSE_NEIGHBOR",
    ]
    dominant_block_id = str(loose["dominant_block_id"])
    median = _finite_float(
        loose["median_dominance_share"], "H_B.loose.median_dominance_share"
    )
    loose_shares = loose["median_share_by_block"]
    tight_shares = tight["median_share_by_block"]
    neighbor_shares = neighbor["median_share_by_block"]
    if not all(isinstance(item, dict) for item in [loose_shares, tight_shares, neighbor_shares]):
        raise ValueError("H_B median_share_by_block must be mappings")
    loose_block_share = _finite_float(
        loose_shares[dominant_block_id], "H_B.loose.block_share"
    )
    tight_block_share = _finite_float(
        tight_shares[dominant_block_id], "H_B.tight.block_share"
    )
    neighbor_block_share = _finite_float(
        neighbor_shares[dominant_block_id], "H_B.neighbor.block_share"
    )
    tight_advantage = loose_block_share - tight_block_share
    neighbor_advantage = loose_block_share - neighbor_block_share
    tight_ratio = _positive_ratio(
        loose_block_share, tight_block_share, "H_B.tight_share_ratio"
    )
    neighbor_ratio = _positive_ratio(
        loose_block_share, neighbor_block_share, "H_B.neighbor_share_ratio"
    )
    necessary = [
        _criterion(
            "H_B_LONGITUDINAL_BLOCK_ID",
            dominant_block_id in threshold["eligible_longitudinal_block_ids"],
            dominant_block_id,
            f"in {threshold['eligible_longitudinal_block_ids']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_B_MEDIAN_DOMINANCE",
            median >= threshold["dominance_share_minimum"],
            median,
            f">={threshold['dominance_share_minimum']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_B_STEP_FRACTION",
            _finite_float(
                loose["dominant_step_fraction"], "H_B.loose.dominant_step_fraction"
            )
            >= threshold["dominant_step_fraction_minimum"],
            loose["dominant_step_fraction"],
            f">={threshold['dominant_step_fraction_minimum']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_B_TIGHT_SHARE_ADVANTAGE",
            tight_advantage >= threshold["median_share_advantage_minimum"],
            tight_advantage,
            f">={threshold['median_share_advantage_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_B_TIGHT_SHARE_RATIO",
            tight_ratio >= threshold["median_share_ratio_minimum"],
            tight_ratio,
            f">={threshold['median_share_ratio_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_B_NEIGHBOR_SHARE_ADVANTAGE",
            neighbor_advantage >= threshold["median_share_advantage_minimum"],
            neighbor_advantage,
            f">={threshold['median_share_advantage_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
        _criterion(
            "H_B_NEIGHBOR_SHARE_RATIO",
            neighbor_ratio >= threshold["median_share_ratio_minimum"],
            neighbor_ratio,
            f">={threshold['median_share_ratio_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
    ]
    return _decision(HYPOTHESES_A_TO_D[1], necessary, [], evidence_ids)


def _evaluate_H_C(metrics: dict[str, Any]) -> dict[str, Any]:
    loose = _role_metric(metrics, "discrete_closure", ROLE_KEYS[0])
    tight = _role_metric(metrics, "discrete_closure", ROLE_KEYS[1])
    neighbor = _role_metric(metrics, "discrete_closure", ROLE_KEYS[2])
    threshold = SUPPORT_CONSTANTS["H_C"]
    evidence_ids = [
        "OBS_DISCRETE_CLOSURE:R13_LOOSE",
        "OBS_DISCRETE_CLOSURE:R13_TIGHT",
        "OBS_DISCRETE_CLOSURE:R10_LOOSE_NEIGHBOR",
    ]
    value = _finite_float(
        loose["max_roundoff_bound_ratio"], "H_C.loose.max_roundoff_bound_ratio"
    )
    tight_value = _finite_float(
        tight["max_roundoff_bound_ratio"], "H_C.tight.max_roundoff_bound_ratio"
    )
    neighbor_value = _finite_float(
        neighbor["max_roundoff_bound_ratio"],
        "H_C.neighbor.max_roundoff_bound_ratio",
    )
    tight_ratio = _positive_ratio(value, tight_value, "H_C.tight_ratio")
    neighbor_ratio = _positive_ratio(value, neighbor_value, "H_C.neighbor_ratio")
    necessary = [
        _criterion(
            "H_C_CLOSURE_MISMATCH",
            value > threshold["roundoff_bound_violation_ratio_strictly_above"],
            value,
            f">{threshold['roundoff_bound_violation_ratio_strictly_above']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_C_CONSECUTIVE_VIOLATIONS",
            int(loose["maximum_consecutive_violation_steps"])
            >= threshold["minimum_consecutive_violation_steps"],
            int(loose["maximum_consecutive_violation_steps"]),
            f">={threshold['minimum_consecutive_violation_steps']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_C_SAMPLE_COUNT",
            int(loose["sample_count"])
            == threshold["required_postinitial_step_count"],
            int(loose["sample_count"]),
            f"=={threshold['required_postinitial_step_count']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_C_TIGHT_CONTRAST",
            tight_ratio >= threshold["loose_to_tight_max_ratio_minimum"],
            tight_ratio,
            f">={threshold['loose_to_tight_max_ratio_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_C_NEIGHBOR_CONTRAST",
            neighbor_ratio >= threshold["loose_to_neighbor_max_ratio_minimum"],
            neighbor_ratio,
            f">={threshold['loose_to_neighbor_max_ratio_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
    ]
    return _decision(HYPOTHESES_A_TO_D[2], necessary, [], evidence_ids)


def _evaluate_H_D(metrics: dict[str, Any]) -> dict[str, Any]:
    loose = _role_metric(metrics, "distributed_accumulation", ROLE_KEYS[0])
    tight = _role_metric(metrics, "distributed_accumulation", ROLE_KEYS[1])
    neighbor = _role_metric(metrics, "distributed_accumulation", ROLE_KEYS[2])
    threshold = SUPPORT_CONSTANTS["H_D"]
    evidence_ids = [
        "OBS_DISTRIBUTED_ACCUMULATION:R13_LOOSE",
        "OBS_DISTRIBUTED_ACCUMULATION:R13_TIGHT",
        "OBS_DISTRIBUTED_ACCUMULATION:R10_LOOSE_NEIGHBOR",
    ]
    fraction = _finite_float(
        loose["distributed_step_fraction"], "H_D.loose.distributed_step_fraction"
    )
    tight_fraction = _finite_float(
        tight["distributed_step_fraction"], "H_D.tight.distributed_step_fraction"
    )
    neighbor_fraction = _finite_float(
        neighbor["distributed_step_fraction"],
        "H_D.neighbor.distributed_step_fraction",
    )
    tight_advantage = fraction - tight_fraction
    neighbor_advantage = fraction - neighbor_fraction
    necessary = [
        _criterion(
            "H_D_DISTRIBUTED_STEP_FRACTION",
            fraction >= threshold["distributed_step_fraction_minimum"],
            fraction,
            f">={threshold['distributed_step_fraction_minimum']}; per-step qualifier is "
            f">={threshold['minimum_contributing_block_count_per_step']} blocks at share "
            f">={threshold['per_block_share_minimum']}, effective count "
            f">={threshold['effective_block_count_minimum']}, and max share "
            f"<{threshold['single_block_share_maximum_exclusive']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_D_TIGHT_DISTRIBUTED_ADVANTAGE",
            tight_advantage
            >= threshold["distributed_fraction_advantage_over_each_reference_minimum"],
            tight_advantage,
            f">={threshold['distributed_fraction_advantage_over_each_reference_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_D_NEIGHBOR_DISTRIBUTED_ADVANTAGE",
            neighbor_advantage
            >= threshold["distributed_fraction_advantage_over_each_reference_minimum"],
            neighbor_advantage,
            f">={threshold['distributed_fraction_advantage_over_each_reference_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
        _criterion(
            "H_D_ALL_LINKED_MAXIMA_AT_FINAL_TIME",
            int(loose["linked_series_maxima_at_final_count"])
            == threshold["linked_structural_series_count"],
            int(loose["linked_series_maxima_at_final_count"]),
            f"=={threshold['linked_structural_series_count']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_D_LINKED_SERIES_ACCUMULATE",
            int(loose["minimum_nondecreasing_increment_count"])
            >= threshold["minimum_nondecreasing_increments_per_series"],
            int(loose["minimum_nondecreasing_increment_count"]),
            f">={threshold['minimum_nondecreasing_increments_per_series']}",
            evidence_ids[:1],
        ),
    ]
    return _decision(HYPOTHESES_A_TO_D[3], necessary, [], evidence_ids)


def classify(evidence: dict[str, Any]) -> dict[str, Any]:
    gate = _gate(evidence)
    if gate is not None:
        return _blocked(*gate)
    try:
        metrics = evidence["metrics"]
        decisions = [
            _evaluate_H_A(metrics),
            _evaluate_H_B(metrics),
            _evaluate_H_C(metrics),
            _evaluate_H_D(metrics),
        ]
    except (KeyError, TypeError, ValueError) as error:
        return _blocked(
            "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
            f"MECHANISM_METRIC_SCHEMA_INVALID:{type(error).__name__}",
        )
    supported = [
        item["hypothesis_id"] for item in decisions if item["status"] == "SUPPORTED"
    ]
    h_e = {
        "hypothesis_id": H_E,
        "status": "NOT_SUPPORTED" if supported else "SUPPORTED",
        "evidence_ids": [
            evidence_id
            for item in decisions
            for evidence_id in item["evidence_ids"]
        ],
        "necessary_condition_decisions": [
            _criterion(
                "H_E_COMPLETE_ADMISSIBLE_EVIDENCE",
                True,
                "EVIDENCE_ADMISSIBLE",
                "==EVIDENCE_ADMISSIBLE",
                [],
            ),
            _criterion(
                "H_E_EMPTY_SUPPORT_SET",
                not supported,
                supported,
                "supported_mechanism_ids == []",
                [],
            ),
        ],
        "supporting_condition_decisions": [],
        "decision_reasons": [
            "complete admissible evidence is nondiscriminating"
            if not supported
            else "one or more positive mechanisms are supported"
        ],
    }
    aggregate = (
        "SINGLE_SUPPORTED_MECHANISM"
        if len(supported) == 1
        else "MULTIPLE_SUPPORTED_MECHANISMS"
        if len(supported) > 1
        else "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    )
    return {
        "classifier_id": CLASSIFIER_ID,
        "evidence_result": "EVIDENCE_ADMISSIBLE",
        "evidence_diagnostic": "NONE",
        "hypothesis_decisions": {
            item["hypothesis_id"]: item for item in decisions + [h_e]
        },
        "supported_mechanism_ids": supported,
        "aggregate_mechanism_result": aggregate,
        "claim_ceiling": CLAIM_CEILING,
    }


def validate_result(result: dict[str, Any]) -> list[str]:
    decisions = result.get("hypothesis_decisions", {})
    if not isinstance(decisions, dict) or list(decisions) != HYPOTHESES_A_TO_D + [H_E]:
        return ["INDIVIDUAL_HYPOTHESIS_DECISIONS_MISSING_OR_UNORDERED"]
    if result.get("aggregate_mechanism_result") == "MULTIPLE_SUPPORTED_MECHANISMS" and (
        "supported_mechanism_ids" not in result
    ):
        return ["MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"]
    expected = [
        hypothesis_id
        for hypothesis_id in HYPOTHESES_A_TO_D
        if decisions.get(hypothesis_id, {}).get("status") == "SUPPORTED"
    ]
    if result.get("supported_mechanism_ids") != expected:
        return ["SUPPORTED_MECHANISM_IDENTITY_SET_MISMATCH"]
    for hypothesis_id in HYPOTHESES_A_TO_D:
        decision = decisions[hypothesis_id]
        if decision.get("status") == "SUPPORTED":
            necessary = decision.get("necessary_condition_decisions")
            if not isinstance(necessary, list) or not necessary or not all(
                item.get("status") == "PASSED" for item in necessary
            ):
                return [f"{hypothesis_id}_AWARDED_WITHOUT_POSITIVE_EVIDENCE"]
    if (
        decisions.get(H_E, {}).get("status") == "SUPPORTED"
        and result.get("evidence_result") != "EVIDENCE_ADMISSIBLE"
    ):
        return ["INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"]
    if result.get("evidence_result") != "EVIDENCE_ADMISSIBLE" and any(
        item.get("status") != "NOT_EVALUATED" for item in decisions.values()
    ):
        return ["CLASSIFICATION_PERFORMED_AFTER_EVIDENCE_BLOCK"]
    expected_aggregate = (
        "BLOCKED"
        if result.get("evidence_result") != "EVIDENCE_ADMISSIBLE"
        else "SINGLE_SUPPORTED_MECHANISM"
        if len(expected) == 1
        else "MULTIPLE_SUPPORTED_MECHANISMS"
        if len(expected) > 1
        else "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    )
    if result.get("aggregate_mechanism_result") != expected_aggregate:
        return ["AGGREGATE_MECHANISM_RESULT_MISMATCH"]
    expected_h_e = (
        "NOT_EVALUATED"
        if result.get("evidence_result") != "EVIDENCE_ADMISSIBLE"
        else "SUPPORTED"
        if not expected
        else "NOT_SUPPORTED"
    )
    if decisions[H_E].get("status") != expected_h_e:
        return ["H_E_PRECEDENCE_OR_COMPLETENESS_MISMATCH"]
    return []


def mutation_controls(admissible_fixture: dict[str, Any]) -> list[dict[str, Any]]:
    controls: list[dict[str, Any]] = []

    def record(mutation_id: str, mutated: dict[str, Any], expected: str) -> None:
        result = classify(mutated)
        actual = result["evidence_diagnostic"]
        controls.append(
            {
                "mutation_id": mutation_id,
                "expected_diagnostic": expected,
                "actual_diagnostic": actual,
                "passed": actual == expected,
            }
        )

    missing = copy.deepcopy(admissible_fixture)
    missing["required_observables_complete"] = False
    record("MISSING_REQUIRED_OBSERVABLE", missing, "REQUIRED_OBSERVABLE_MISSING")

    perturbed = copy.deepcopy(admissible_fixture)
    perturbed["instrumentation_nonperturbation_passed"] = False
    record(
        "INSTRUMENTED_TRAJECTORY_CHANGED",
        perturbed,
        "INSTRUMENTED_TRAJECTORY_NOT_BYTE_IDENTICAL",
    )

    continuum = copy.deepcopy(admissible_fixture)
    continuum["discrete_operator_binding_passed"] = False
    record(
        "CONTINUUM_OPERATOR_SUBSTITUTED",
        continuum,
        "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED",
    )

    output_collision = copy.deepcopy(admissible_fixture)
    output_collision["separate_output_custody_passed"] = False
    record(
        "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL",
        output_collision,
        "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL",
    )

    duplicate = copy.deepcopy(admissible_fixture)
    duplicate["observed_run_ids"][1] = duplicate["observed_run_ids"][0]
    record("DUPLICATE_RUN_ID", duplicate, "DUPLICATE_RUN_IDENTITY")

    unknown = copy.deepcopy(admissible_fixture)
    unknown["observed_run_ids"][-1] = "MECHv0:UNKNOWN"
    record("UNKNOWN_RUN_ID", unknown, "EXPECTED_RUN_ID_CLOSURE_MISMATCH")
    return controls
