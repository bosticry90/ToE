from __future__ import annotations

"""Raw-payload-only classifier for the R13 mechanism experiment.

The sole public classification entry point accepts filesystem paths, invokes
the strict v2 evidence assembler, and evaluates H_A--H_D only from metrics
recomputed from the twelve registered JSON/NPZ payloads.  There is intentionally
no ``classify(evidence_dict)`` API: caller-supplied gates, booleans, run IDs,
payload IDs, summaries, or mechanism metrics cannot enter the decision path.
"""

import math
from pathlib import Path
from typing import Any, Mapping

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v2
    as raw_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1
    as semantic_v1,
)


CLASSIFIER_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_CLASSIFIER_v2"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_classifier_v2.py"
)
HYPOTHESES_A_TO_D = (
    "H_A_CANCELLATION_CONDITIONING",
    "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
    "H_C_DISCRETE_CLOSURE_MISMATCH",
    "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
)
H_E = "H_E_UNRESOLVED_MECHANISM"
ROLE_KEYS = ("R13_LOOSE", "R13_TIGHT", "R10_LOOSE_NEIGHBOR")
SUPPORT_CONSTANTS = semantic_v1.SUPPORT_CONSTANTS_V1
SUPPORT_CONSTANT_PROVENANCE = semantic_v1.SUPPORT_CONSTANT_PROVENANCE
CLASSIFIER_PRECEDENCE = (
    "assemble and authenticate exact frozen documents and implementation closure",
    "authenticate exact six-run and twelve-payload identity closure",
    "decode every JSON/NPZ raw array and validate finite shapes and schemas",
    "recompute and hard-gate instrumentation trajectory byte identity",
    "recompute units, normalizations, solver blocks, and operator intermediates",
    "reconstruct independent H_C paths; keep legacy Q operator-gate-only",
    "evaluate H_A independently from raw exchange-cell arrays",
    "evaluate H_B independently from raw terminal packed defects",
    "evaluate H_C independently from direct terminal Rp and Dirac-current path",
    "evaluate H_D independently from raw block shares and structural histories",
    "preserve individual decisions and ordered supported_mechanism_ids",
    "assign H_E only after complete admissible evidence and an empty support set",
    "apply the numerical-mechanism-only claim ceiling",
)
CLAIM_CEILING = (
    "NUMERICAL_MECHANISM_EVIDENCE_ONLY; no robustness reclassification, "
    "materiality evaluation, physical instability, model-domain boundary, "
    "E-REPRO, pillar, seam, C_k, CCFT, or master-action promotion"
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
    evidence_ids: list[str],
) -> dict[str, Any]:
    supported = bool(necessary) and all(
        item["status"] == "PASSED" for item in necessary
    )
    return {
        "hypothesis_id": hypothesis_id,
        "status": "SUPPORTED" if supported else "NOT_SUPPORTED",
        "evidence_ids": list(dict.fromkeys(evidence_ids)),
        "necessary_condition_decisions": necessary,
        "supporting_condition_decisions": [],
        "decision_reasons": [item["reason"] for item in necessary],
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


def _blocked(
    evidence_result: str,
    diagnostic: str,
    detail: str = "",
) -> dict[str, Any]:
    return {
        "classifier_id": CLASSIFIER_ID,
        "assembler_id": raw_v2.ASSEMBLER_ID,
        "semantic_contract_id": semantic_v1.CONTRACT_ID,
        "evidence_result": evidence_result,
        "evidence_diagnostic": diagnostic,
        "evidence_detail": detail,
        "hypothesis_decisions": {
            hypothesis_id: _not_evaluated(hypothesis_id, evidence_result)
            for hypothesis_id in HYPOTHESES_A_TO_D + (H_E,)
        },
        "supported_mechanism_ids": [],
        "aggregate_mechanism_result": "BLOCKED",
        "claim_ceiling": CLAIM_CEILING,
        "classifier_precedence": list(CLASSIFIER_PRECEDENCE),
    }


def _role_metric(
    metrics: Mapping[str, Mapping[str, Mapping[str, Any]]],
    family: str,
    role: str,
) -> Mapping[str, Any]:
    family_metrics = metrics.get(family)
    if not isinstance(family_metrics, Mapping):
        raise ValueError(f"missing recomputed metric family {family}")
    value = family_metrics.get(role)
    if not isinstance(value, Mapping):
        raise ValueError(f"missing recomputed metric {family}:{role}")
    return value


def _finite_float(value: Any, field: str) -> float:
    if isinstance(value, bool):
        raise ValueError(f"boolean metric {field}")
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


def _directional_log10_contrast(
    loose: float, reference: float, field: str
) -> float:
    if loose < 0.0 or reference < 0.0:
        raise ValueError(f"negative log contrast operand {field}")
    result = math.log10(max(loose, 1.0) / max(reference, 1.0))
    if not math.isfinite(result):
        raise ValueError(f"nonfinite log contrast {field}")
    return result


def _evaluate_h_a(
    metrics: Mapping[str, Mapping[str, Mapping[str, Any]]]
) -> dict[str, Any]:
    loose = _role_metric(metrics, "exchange_conditioning", ROLE_KEYS[0])
    tight = _role_metric(metrics, "exchange_conditioning", ROLE_KEYS[1])
    neighbor = _role_metric(metrics, "exchange_conditioning", ROLE_KEYS[2])
    constants = SUPPORT_CONSTANTS["H_A"]
    evidence_ids = [
        "RAW_EXCHANGE_CELL_ARRAYS:R13_LOOSE",
        "RAW_EXCHANGE_CELL_ARRAYS:R13_TIGHT",
        "RAW_EXCHANGE_CELL_ARRAYS:R10_LOOSE_NEIGHBOR",
    ]
    loose_kappa = _finite_float(loose["median_kappa"], "H_A.loose.median_kappa")
    tight_kappa = _finite_float(tight["median_kappa"], "H_A.tight.median_kappa")
    neighbor_kappa = _finite_float(
        neighbor["median_kappa"], "H_A.neighbor.median_kappa"
    )
    tight_contrast = _directional_log10_contrast(
        loose_kappa, tight_kappa, "H_A.tight_contrast"
    )
    neighbor_contrast = _directional_log10_contrast(
        loose_kappa, neighbor_kappa, "H_A.neighbor_contrast"
    )
    necessary = [
        _criterion(
            "H_A_KAPPA_MATERIAL",
            loose_kappa >= constants["loose_median_kappa_minimum"],
            loose_kappa,
            f">={constants['loose_median_kappa_minimum']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_A_SEVERE_STEP_PERSISTENCE",
            _finite_float(
                loose["severe_step_fraction"], "H_A.loose.severe_step_fraction"
            )
            >= constants["severe_step_fraction_minimum"],
            loose["severe_step_fraction"],
            f">={constants['severe_step_fraction_minimum']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_A_COMPLETE_STEP_SERIES",
            int(loose["sample_count"])
            == constants["required_postinitial_step_count"],
            int(loose["sample_count"]),
            f"=={constants['required_postinitial_step_count']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_A_TIGHT_DIRECTIONAL_CONTRAST",
            tight_contrast >= constants["directional_log10_contrast_minimum"],
            tight_contrast,
            f">={constants['directional_log10_contrast_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_A_NEIGHBOR_DIRECTIONAL_CONTRAST",
            neighbor_contrast
            >= constants["directional_log10_contrast_minimum"],
            neighbor_contrast,
            f">={constants['directional_log10_contrast_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
    ]
    return _decision(HYPOTHESES_A_TO_D[0], necessary, evidence_ids)


def _evaluate_h_b(
    metrics: Mapping[str, Mapping[str, Mapping[str, Any]]]
) -> dict[str, Any]:
    loose = _role_metric(metrics, "block_dominance", ROLE_KEYS[0])
    tight = _role_metric(metrics, "block_dominance", ROLE_KEYS[1])
    neighbor = _role_metric(metrics, "block_dominance", ROLE_KEYS[2])
    constants = SUPPORT_CONSTANTS["H_B"]
    evidence_ids = [
        "RAW_TERMINAL_PACKED_DEFECTS:R13_LOOSE",
        "RAW_TERMINAL_PACKED_DEFECTS:R13_TIGHT",
        "RAW_TERMINAL_PACKED_DEFECTS:R10_LOOSE_NEIGHBOR",
    ]
    block_id = str(loose["dominant_block_id"])
    if block_id not in raw_v2.BLOCK_IDS:
        raise ValueError("unknown dominant solver block")
    loose_shares = loose["median_share_by_block"]
    tight_shares = tight["median_share_by_block"]
    neighbor_shares = neighbor["median_share_by_block"]
    if not all(isinstance(value, Mapping) for value in (loose_shares, tight_shares, neighbor_shares)):
        raise ValueError("median_share_by_block must be mappings")
    if any(set(value) != set(raw_v2.BLOCK_IDS) for value in (loose_shares, tight_shares, neighbor_shares)):
        raise ValueError("unknown or missing solver block")
    loose_share = _finite_float(loose_shares[block_id], "H_B.loose.block_share")
    tight_share = _finite_float(tight_shares[block_id], "H_B.tight.block_share")
    neighbor_share = _finite_float(
        neighbor_shares[block_id], "H_B.neighbor.block_share"
    )
    tight_advantage = loose_share - tight_share
    neighbor_advantage = loose_share - neighbor_share
    tight_ratio = _positive_ratio(loose_share, tight_share, "H_B.tight_ratio")
    neighbor_ratio = _positive_ratio(
        loose_share, neighbor_share, "H_B.neighbor_ratio"
    )
    median = _finite_float(
        loose["median_dominance_share"], "H_B.loose.median_dominance_share"
    )
    necessary = [
        _criterion(
            "H_B_LONGITUDINAL_BLOCK_ID",
            block_id in constants["eligible_longitudinal_block_ids"],
            block_id,
            f"in {constants['eligible_longitudinal_block_ids']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_B_MEDIAN_DOMINANCE",
            median >= constants["dominance_share_minimum"],
            median,
            f">={constants['dominance_share_minimum']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_B_STEP_FRACTION",
            _finite_float(
                loose["dominant_step_fraction"], "H_B.loose.dominant_step_fraction"
            )
            >= constants["dominant_step_fraction_minimum"],
            loose["dominant_step_fraction"],
            f">={constants['dominant_step_fraction_minimum']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_B_TIGHT_SHARE_ADVANTAGE",
            tight_advantage >= constants["median_share_advantage_minimum"],
            tight_advantage,
            f">={constants['median_share_advantage_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_B_TIGHT_SHARE_RATIO",
            tight_ratio >= constants["median_share_ratio_minimum"],
            tight_ratio,
            f">={constants['median_share_ratio_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_B_NEIGHBOR_SHARE_ADVANTAGE",
            neighbor_advantage >= constants["median_share_advantage_minimum"],
            neighbor_advantage,
            f">={constants['median_share_advantage_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
        _criterion(
            "H_B_NEIGHBOR_SHARE_RATIO",
            neighbor_ratio >= constants["median_share_ratio_minimum"],
            neighbor_ratio,
            f">={constants['median_share_ratio_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
    ]
    return _decision(HYPOTHESES_A_TO_D[1], necessary, evidence_ids)


def _evaluate_h_c(
    metrics: Mapping[str, Mapping[str, Mapping[str, Any]]]
) -> dict[str, Any]:
    family = "independent_discrete_closure"
    loose = _role_metric(metrics, family, ROLE_KEYS[0])
    tight = _role_metric(metrics, family, ROLE_KEYS[1])
    neighbor = _role_metric(metrics, family, ROLE_KEYS[2])
    constants = SUPPORT_CONSTANTS["H_C"]
    evidence_ids = [
        "DIRECT_TERMINAL_RP_AND_INDEPENDENT_DIRAC_CURRENT:R13_LOOSE",
        "DIRECT_TERMINAL_RP_AND_INDEPENDENT_DIRAC_CURRENT:R13_TIGHT",
        "DIRECT_TERMINAL_RP_AND_INDEPENDENT_DIRAC_CURRENT:R10_LOOSE_NEIGHBOR",
    ]
    for role, value in zip(ROLE_KEYS, (loose, tight, neighbor), strict=True):
        if (
            value.get("legacy_q_used") is not False
            or value.get("mechanism_path_sources_independent") is not True
        ):
            raise ValueError(f"H_C independent path contract failed for {role}")
    loose_value = _finite_float(
        loose["max_relative_path_mismatch"],
        "H_C.loose.max_relative_path_mismatch",
    )
    tight_value = _finite_float(
        tight["max_relative_path_mismatch"],
        "H_C.tight.max_relative_path_mismatch",
    )
    neighbor_value = _finite_float(
        neighbor["max_relative_path_mismatch"],
        "H_C.neighbor.max_relative_path_mismatch",
    )
    tight_ratio = _positive_ratio(loose_value, tight_value, "H_C.tight_ratio")
    neighbor_ratio = _positive_ratio(
        loose_value, neighbor_value, "H_C.neighbor_ratio"
    )
    necessary = [
        _criterion(
            "H_C_INDEPENDENT_PATH_MISMATCH",
            loose_value >= constants["relative_path_mismatch_minimum"],
            loose_value,
            f">={constants['relative_path_mismatch_minimum']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_C_CONSECUTIVE_PATH_MISMATCH",
            int(loose["maximum_consecutive_mismatch_steps"])
            >= constants["minimum_consecutive_mismatch_steps"],
            int(loose["maximum_consecutive_mismatch_steps"]),
            f">={constants['minimum_consecutive_mismatch_steps']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_C_COMPLETE_INDEPENDENT_PATH_SERIES",
            int(loose["sample_count"])
            == constants["required_postinitial_step_count"],
            int(loose["sample_count"]),
            f"=={constants['required_postinitial_step_count']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_C_TIGHT_PATH_CONTRAST",
            tight_ratio >= constants["loose_to_tight_max_ratio_minimum"],
            tight_ratio,
            f">={constants['loose_to_tight_max_ratio_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_C_NEIGHBOR_PATH_CONTRAST",
            neighbor_ratio >= constants["loose_to_neighbor_max_ratio_minimum"],
            neighbor_ratio,
            f">={constants['loose_to_neighbor_max_ratio_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
    ]
    return _decision(HYPOTHESES_A_TO_D[2], necessary, evidence_ids)


def _evaluate_h_d(
    metrics: Mapping[str, Mapping[str, Mapping[str, Any]]]
) -> dict[str, Any]:
    loose = _role_metric(metrics, "distributed_accumulation", ROLE_KEYS[0])
    tight = _role_metric(metrics, "distributed_accumulation", ROLE_KEYS[1])
    neighbor = _role_metric(
        metrics, "distributed_accumulation", ROLE_KEYS[2]
    )
    constants = SUPPORT_CONSTANTS["H_D"]
    evidence_ids = [
        "RAW_BLOCK_SHARES_AND_STRUCTURAL_SERIES:R13_LOOSE",
        "RAW_BLOCK_SHARES_AND_STRUCTURAL_SERIES:R13_TIGHT",
        "RAW_BLOCK_SHARES_AND_STRUCTURAL_SERIES:R10_LOOSE_NEIGHBOR",
    ]
    loose_fraction = _finite_float(
        loose["distributed_step_fraction"], "H_D.loose.distributed_step_fraction"
    )
    tight_fraction = _finite_float(
        tight["distributed_step_fraction"], "H_D.tight.distributed_step_fraction"
    )
    neighbor_fraction = _finite_float(
        neighbor["distributed_step_fraction"],
        "H_D.neighbor.distributed_step_fraction",
    )
    tight_advantage = loose_fraction - tight_fraction
    neighbor_advantage = loose_fraction - neighbor_fraction
    necessary = [
        _criterion(
            "H_D_DISTRIBUTED_STEP_FRACTION",
            loose_fraction >= constants["distributed_step_fraction_minimum"],
            loose_fraction,
            f">={constants['distributed_step_fraction_minimum']}; >="
            f"{constants['minimum_contributing_block_count_per_step']} blocks at "
            f"share>={constants['per_block_share_minimum']}, effective count>="
            f"{constants['effective_block_count_minimum']}, max share<"
            f"{constants['single_block_share_maximum_exclusive']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_D_TIGHT_DISTRIBUTED_ADVANTAGE",
            tight_advantage
            >= constants[
                "distributed_fraction_advantage_over_each_reference_minimum"
            ],
            tight_advantage,
            f">={constants['distributed_fraction_advantage_over_each_reference_minimum']}",
            evidence_ids[:2],
        ),
        _criterion(
            "H_D_NEIGHBOR_DISTRIBUTED_ADVANTAGE",
            neighbor_advantage
            >= constants[
                "distributed_fraction_advantage_over_each_reference_minimum"
            ],
            neighbor_advantage,
            f">={constants['distributed_fraction_advantage_over_each_reference_minimum']}",
            [evidence_ids[0], evidence_ids[2]],
        ),
        _criterion(
            "H_D_ALL_LINKED_MAXIMA_AT_FINAL_TIME",
            int(loose["linked_series_maxima_at_final_count"])
            == constants["linked_structural_series_count"],
            int(loose["linked_series_maxima_at_final_count"]),
            f"=={constants['linked_structural_series_count']}",
            evidence_ids[:1],
        ),
        _criterion(
            "H_D_LINKED_SERIES_ACCUMULATE",
            int(loose["minimum_nondecreasing_increment_count"])
            >= constants["minimum_nondecreasing_increments_per_series"],
            int(loose["minimum_nondecreasing_increment_count"]),
            f">={constants['minimum_nondecreasing_increments_per_series']}",
            evidence_ids[:1],
        ),
    ]
    return _decision(HYPOTHESES_A_TO_D[3], necessary, evidence_ids)


def _classify_assembled(evidence: raw_v2.AssembledRawEvidence) -> dict[str, Any]:
    metrics = evidence.recomputed_metrics
    decisions = [
        _evaluate_h_a(metrics),
        _evaluate_h_b(metrics),
        _evaluate_h_c(metrics),
        _evaluate_h_d(metrics),
    ]
    supported = [
        decision["hypothesis_id"]
        for decision in decisions
        if decision["status"] == "SUPPORTED"
    ]
    expected_supported = [
        hypothesis_id
        for hypothesis_id in HYPOTHESES_A_TO_D
        if next(
            decision for decision in decisions if decision["hypothesis_id"] == hypothesis_id
        )["status"]
        == "SUPPORTED"
    ]
    if supported != expected_supported:
        raise ValueError("supported mechanism identity set invariant failed")
    h_e_supported = not supported
    h_e_criteria = [
        _criterion(
            "H_E_COMPLETE_ADMISSIBLE_RAW_EVIDENCE",
            True,
            "EVIDENCE_ADMISSIBLE",
            "==EVIDENCE_ADMISSIBLE",
            list(evidence.raw_evidence_ids),
        ),
        _criterion(
            "H_E_EMPTY_SUPPORT_SET",
            h_e_supported,
            list(supported),
            "==[]",
            list(evidence.raw_evidence_ids),
        ),
    ]
    h_e = {
        "hypothesis_id": H_E,
        "status": "SUPPORTED" if h_e_supported else "NOT_SUPPORTED",
        "evidence_ids": list(evidence.raw_evidence_ids),
        "necessary_condition_decisions": h_e_criteria,
        "supporting_condition_decisions": [],
        "decision_reasons": [item["reason"] for item in h_e_criteria],
    }
    aggregate = (
        "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
        if not supported
        else "SINGLE_SUPPORTED_MECHANISM"
        if len(supported) == 1
        else "MULTIPLE_SUPPORTED_MECHANISMS"
    )
    return {
        "classifier_id": CLASSIFIER_ID,
        "assembler_id": evidence.assembler_id,
        "semantic_contract_id": evidence.semantic_contract_id,
        "evidence_result": "EVIDENCE_ADMISSIBLE",
        "evidence_diagnostic": "RAW_EVIDENCE_RECOMPUTED_AND_ADMISSIBLE",
        "evidence_detail": "",
        "run_ids": list(evidence.run_ids),
        "payload_identity_ids": list(evidence.payload_identity_ids),
        "raw_evidence_ids": list(evidence.raw_evidence_ids),
        "supplied_summary_disposition": evidence.supplied_summary_disposition,
        "canonical_tree_sha256": evidence.canonical_tree_sha256,
        "review_anchor_sha256": evidence.review_anchor_sha256,
        "runtime_source_closure_sha256": (
            evidence.runtime_source_closure_sha256
        ),
        "recomputed_metrics": metrics,
        "hypothesis_decisions": {
            decision["hypothesis_id"]: decision
            for decision in decisions + [h_e]
        },
        "supported_mechanism_ids": supported,
        "aggregate_mechanism_result": aggregate,
        "support_constant_provenance": list(SUPPORT_CONSTANT_PROVENANCE),
        "claim_ceiling": CLAIM_CEILING,
        "classifier_precedence": list(CLASSIFIER_PRECEDENCE),
    }


def classify_from_raw_payloads(
    repo_root: str | Path,
) -> dict[str, Any]:
    """Classify one completed experiment exclusively from registered files."""

    try:
        assembled = raw_v2.assemble_raw_evidence(
            repo_root,
        )
    except raw_v2.RawEvidenceError as error:
        return _blocked(error.evidence_result, error.diagnostic, error.detail)
    try:
        return _classify_assembled(assembled)
    except (KeyError, TypeError, ValueError) as error:
        return _blocked(
            "BLOCKED_OBSERVABLE_SEMANTICS",
            "RECOMPUTED_MECHANISM_METRIC_SCHEMA_INVALID",
            f"{type(error).__name__}:{error}",
        )


def self_validate() -> dict[str, bool]:
    return {
        "exact_23_support_constants": sum(
            len(values) for values in SUPPORT_CONSTANTS.values()
        )
        == 23,
        "exact_23_provenance_records": len(SUPPORT_CONSTANT_PROVENANCE) == 23,
        "h_c_has_no_gamma_constant": all(
            "gamma" not in key.lower() for key in SUPPORT_CONSTANTS["H_C"]
        ),
        "legacy_q_not_decision_bearing": semantic_v1.LEGACY_Q[
            "mechanism_decision_bearing"
        ]
        is False,
        "h_e_follows_raw_assembly": CLASSIFIER_PRECEDENCE.index(
            "assign H_E only after complete admissible evidence and an empty support set"
        )
        > CLASSIFIER_PRECEDENCE.index(
            "evaluate H_D independently from raw block shares and structural histories"
        ),
        "no_public_summary_classifier": "classify" not in __all__,
    }


__all__ = [
    "CLASSIFIER_ID",
    "SUPPORT_CONSTANTS",
    "SUPPORT_CONSTANT_PROVENANCE",
    "classify_from_raw_payloads",
    "self_validate",
]
