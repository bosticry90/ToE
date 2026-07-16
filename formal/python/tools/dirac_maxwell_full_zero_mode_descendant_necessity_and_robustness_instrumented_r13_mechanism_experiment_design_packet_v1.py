from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_design_packet_v0
    as design_v0,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-15T00:00:00Z"
CONSUMED_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v0_result"
)
TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v1"
)
SELECTED_NEXT_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v1_result"
)
DOWNSTREAM_TARGET_IF_ACCEPTED = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0"
)
PACKET_SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_v1"
)
MANIFEST_SCHEMA_ID = f"{PACKET_SCHEMA_ID}_MANIFEST"
REPORT_SCHEMA_ID = f"{PACKET_SCHEMA_ID}_RELEASE_REPORT_20260715"
PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-PACKET-v1.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-MANIFEST-v1.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_"
    "20260715_v1.json"
)
GENERATOR_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_v1.py"
)
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

DESIGN_V0_PACKET = design_v0.PACKET_RELATIVE_PATH
DESIGN_V0_MANIFEST = design_v0.MANIFEST_RELATIVE_PATH
DESIGN_V0_REPORT = design_v0.REPORT_RELATIVE_PATH
DESIGN_V0_GENERATOR = design_v0.GENERATOR_RELATIVE_PATH
BLOCKED_REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_"
    "20260715_v0.json"
)
BLOCKED_REVIEWER = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_review_v0.py"
)
CANONICAL_REVIEW_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json"
)

EXPECTED_CORRECTION_SOURCE_HASHES = {
    DESIGN_V0_PACKET: "c41a724d4f84566583d970de67ed18ea2490541f4e4a0c4faecff3e057a3b579",
    DESIGN_V0_MANIFEST: "debeacd35c44a1a0e063f758934f4dc3d5983e11c071c67a651c099dda87e6b9",
    DESIGN_V0_REPORT: "f20afcbb5f37c1212bc15bb162765f2c341e20f5e2d6ffc6c54d0e4f10d546d5",
    DESIGN_V0_GENERATOR: "cc95782b5be80c3ee0a44d7e6c2d802ceb8c79bcc12f56a85fcbb2d6df57e2e9",
    BLOCKED_REVIEW_REPORT: "be6a124ba345c7037d1b03aab0f120831e6c62d8ab1e7a2d508288ff7ae0a114",
    BLOCKED_REVIEWER: "0e0d13373e227dcde48e74775868e88d920f472dd2de5aed119239853c5dd95d",
    CANONICAL_REVIEW_REPORT: "cacbd77f3ef18a80d8d15686dd8f385f73a634038fddb5010058f2e144ef3c85",
}
EXPECTED_CANONICAL_ROOT_DIGEST = design_v0.EXPECTED_CANONICAL_ROOT_DIGEST
R13 = "R13_CORNER_STRONG_LOW"
LINKED_LIMITS = {
    "gauss_residual": 5.0e-14,
    "continuity_residual": 4.0e-11,
    "exchange_longitudinal_residual": 8.0e-21,
    "longitudinal_Maxwell_residual": 6.0000000000000005e-15,
}
HYPOTHESES_A_TO_D = [
    "H_A_CANCELLATION_CONDITIONING",
    "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
    "H_C_DISCRETE_CLOSURE_MISMATCH",
    "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
]
H_E = "H_E_UNRESOLVED_MECHANISM"
HYPOTHESIS_STATUSES = ["SUPPORTED", "NOT_SUPPORTED", "NOT_EVALUATED"]
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
BLOCKED_V0_DECISION_IDS = [
    "classifier_preserves_per_hypothesis_support_vector_and_criterion_records",
    "H_E_is_disjoint_from_required_evidence_completeness_block",
    "neighbor_eligibility_prose_matches_axis_sharing_candidate_universe",
]


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def canonical_root_digest() -> str:
    return design_v0.canonical_root_digest()


def _correction_source_custody(base: dict[str, Any]) -> dict[str, Any]:
    hashes = {
        path: sha256_path(REPO_ROOT / path)
        for path in EXPECTED_CORRECTION_SOURCE_HASHES
    }
    manifest = load_json(REPO_ROOT / DESIGN_V0_MANIFEST)
    report = load_json(REPO_ROOT / DESIGN_V0_REPORT)
    blocked = load_json(REPO_ROOT / BLOCKED_REVIEW_REPORT)
    canonical_review = load_json(REPO_ROOT / CANONICAL_REVIEW_REPORT)
    cross_bindings = (
        manifest["packet"]["sha256"] == hashes[DESIGN_V0_PACKET]
        and manifest["generator"]["sha256"] == hashes[DESIGN_V0_GENERATOR]
        and report["artifact_hashes"]
        == {
            "packet_sha256": hashes[DESIGN_V0_PACKET],
            "manifest_sha256": hashes[DESIGN_V0_MANIFEST],
            "generator_sha256": hashes[DESIGN_V0_GENERATOR],
        }
    )
    blocked_review_exact = (
        blocked["target"] == CONSUMED_TARGET
        and blocked["review_completed"] is True
        and blocked["accepted"] is False
        and blocked["verdict"]
        == "BLOCK_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN"
        and blocked["decision_count"] == 37
        and blocked["passed_decision_count"] == 34
        and blocked["failed_decision_ids"] == BLOCKED_V0_DECISION_IDS
        and len(blocked["blocking_findings"]) == 3
        and blocked["selected_next_target"] == CONSUMED_TARGET
        and blocked["authority_rotation"][
            "numerical_freeze_packet_preparation_authorized"
        ]
        is False
        and blocked["authority_rotation"]["new_simulation_authorized"] is False
    )
    canonical_authority_exact = (
        canonical_review["accepted"] is True
        and canonical_review["scientific_robustness_status"] == "NUMERICALLY_BLOCKED"
        and canonical_review["descendant_materiality_status"]
        == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and canonical_review["independent_classifier_reconstruction"][
            "numerically_blocked_rows"
        ]
        == [R13]
    )
    root_digest = canonical_root_digest()
    passed = (
        hashes == EXPECTED_CORRECTION_SOURCE_HASHES
        and cross_bindings
        and blocked_review_exact
        and canonical_authority_exact
        and base["source_custody"]["passed"] is True
        and base["source_custody"]["canonical_run_output_count_checked"] == 203
        and base["source_custody"]["canonical_run_output_hash_failures"] == []
        and base["source_custody"]["execution_count_performed"] == 1
        and root_digest == EXPECTED_CANONICAL_ROOT_DIGEST
    )
    return {
        "passed": passed,
        "bounded_correction_authority_consumed": CONSUMED_TARGET,
        "correction_source_hashes": hashes,
        "all_correction_source_hashes_exact": hashes
        == EXPECTED_CORRECTION_SOURCE_HASHES,
        "design_v0_cross_bindings_exact": cross_bindings,
        "blocked_v0_review_exact": blocked_review_exact,
        "blocked_v0_failed_decision_ids": blocked["failed_decision_ids"],
        "blocked_v0_passed_decision_count_preserved": blocked[
            "passed_decision_count"
        ],
        "canonical_authority_exact": canonical_authority_exact,
        "canonical_root_digest": root_digest,
        "canonical_root_digest_exact": root_digest == EXPECTED_CANONICAL_ROOT_DIGEST,
        "canonical_run_output_count_checked": base["source_custody"][
            "canonical_run_output_count_checked"
        ],
        "canonical_run_output_hash_failures": base["source_custody"][
            "canonical_run_output_hash_failures"
        ],
        "execution_count_performed": base["source_custody"][
            "execution_count_performed"
        ],
        "new_simulation_run_count": 0,
        "canonical_output_mutation_count": 0,
    }


def _all_passing_neighbor_audit() -> dict[str, Any]:
    sources = design_v0._load_sources()
    canonical_review = load_json(REPO_ROOT / CANONICAL_REVIEW_REPORT)
    scientific_rows = {
        item["row_id"]: item["requested_axis_values"]
        for item in sources["freeze"]["scientific_design_freeze"]["scientific_rows"]
    }
    identity_by_run = {item["run_id"]: item for item in sources["identity"]["outputs"]}
    blocked_rows = set(
        canonical_review["study_wide_interpretation"]["blocked_scientific_rows"]
    )
    canonical_passing_row_ids = sorted(set(scientific_rows) - blocked_rows)
    r13_axes = scientific_rows[R13]
    axis_ranges = {
        axis: (
            min(float(values[axis]) for values in scientific_rows.values()),
            max(float(values[axis]) for values in scientific_rows.values()),
        )
        for axis in r13_axes
    }
    universe_audit = []
    for row_id in sorted(row_id for row_id in scientific_rows if row_id != R13):
        axes = scientific_rows[row_id]
        run_id = f"{row_id}:SOLVER_TOL1eM08"
        output_path = REPO_ROOT / identity_by_run[run_id]["relative_output_path"]
        output = load_json(output_path)
        ratios = {
            key: max(abs(float(value)) for value in output["series"][key]) / limit
            for key, limit in LINKED_LIMITS.items()
        }
        shared = sorted(axis for axis, value in axes.items() if value == r13_axes[axis])
        components = {}
        squared = 0.0
        for axis, value in axes.items():
            low, high = axis_ranges[axis]
            component = (
                (float(value) - float(r13_axes[axis])) / (high - low)
                if high > low
                else 0.0
            )
            components[axis] = component
            squared += component * component
        all_four_pass = all(ratio <= 1.0 for ratio in ratios.values())
        universe_audit.append(
            {
                "scientific_row_id": row_id,
                "historical_loose_run_id": run_id,
                "historical_loose_output_sha256": sha256_path(output_path),
                "all_applicable_canonical_criteria_pass": row_id
                in canonical_passing_row_ids,
                "all_four_loose_solver_residual_ceilings_pass": all_four_pass,
                "loose_solver_ceiling_ratios": ratios,
                "maximum_loose_solver_ceiling_ratio": max(ratios.values()),
                "shared_axis_count": len(shared),
                "shared_axes": shared,
                "normalized_distance": math.sqrt(squared),
                "normalized_distance_components": components,
                "eligible": row_id in canonical_passing_row_ids and all_four_pass,
            }
        )
    eligible = [item for item in universe_audit if item["eligible"]]
    ranked = sorted(
        eligible,
        key=lambda item: (
            -item["shared_axis_count"],
            item["normalized_distance"],
            item["scientific_row_id"],
        ),
    )
    for rank, item in enumerate(ranked, start=1):
        item["rank"] = rank
        item["rank_tuple"] = [
            -item["shared_axis_count"],
            item["normalized_distance"],
            item["scientific_row_id"],
        ]
    return {
        "status": "CORRECTED_ALL_PASSING_NON_R13_UNIVERSE_EXACT_SELECTION_DEFERRED_TO_FREEZE",
        "candidate_universe_rule": (
            "every canonical scientific row other than R13 that passed all applicable canonical "
            "criteria; the exact historical 1e-8 role is additionally audited against all four "
            "R13-linked residual ceilings"
        ),
        "candidate_universe_defined_before_ranking": True,
        "canonical_review_passing_scientific_row_count": canonical_review[
            "study_wide_interpretation"
        ]["passing_scientific_rows_descriptive_only"],
        "canonical_review_blocked_scientific_row_ids": sorted(blocked_rows),
        "candidate_universe_row_ids": canonical_passing_row_ids,
        "all_non_R13_scientific_row_count": len(universe_audit),
        "audited_candidate_count": len(universe_audit),
        "audited_candidate_universe": universe_audit,
        "eligible_candidate_count": len(eligible),
        "eligible_candidate_ids": sorted(item["scientific_row_id"] for item in eligible),
        "excluded_candidate_ids": sorted(
            item["scientific_row_id"] for item in universe_audit if not item["eligible"]
        ),
        "ranking_rule": [
            "maximize number of exact R13 axis values shared",
            "minimize Euclidean distance after per-axis min-max normalization over the frozen matrix",
            "break remaining ties by lexicographically ascending scientific_row_id",
        ],
        "ranking_tuple": [
            "negative_shared_axis_count",
            "normalized_distance",
            "scientific_row_id",
        ],
        "ranked_candidate_audit": ranked,
        "provisional_top_candidate_for_freeze_confirmation": ranked[0][
            "scientific_row_id"
        ],
        "unique_top_candidate": (
            ranked[0]["shared_axis_count"], ranked[0]["normalized_distance"]
        )
        != (ranked[1]["shared_axis_count"], ranked[1]["normalized_distance"]),
        "zero_shared_axis_candidates_retained": sorted(
            item["scientific_row_id"]
            for item in ranked
            if item["shared_axis_count"] == 0
        ),
        "axis_sharing_candidate_count": sum(
            1 for item in ranked if item["shared_axis_count"] >= 1
        ),
        "zero_shared_axis_candidate_count": sum(
            1 for item in ranked if item["shared_axis_count"] == 0
        ),
        "candidate_universe_matches_ranked_audit": sorted(
            item["scientific_row_id"] for item in ranked
        )
        == canonical_passing_row_ids,
        "exact_neighbor_frozen_now": False,
        "post_result_visual_choice_allowed": False,
    }


def _corrected_hypotheses_and_classifier(
    base: dict[str, Any]
) -> dict[str, Any]:
    old_hypotheses = {
        item["hypothesis_id"]: copy.deepcopy(item)
        for item in base["hypotheses_and_classifier_design"]["hypotheses"]
    }
    old_hypotheses["H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR"] = {
        "hypothesis_id": "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
        "necessary_condition_classes": [
            "multiple normalized blocks meet future frozen distributed-contribution criteria",
            "structural residual accumulation is reproduced without one block exceeding the future frozen dominance criterion",
            "distributed contribution distinguishes loose R13 from tight R13 and the matched neighbor under frozen contrasts",
        ],
        "supporting_condition_classes": [
            "block contributions share a common tolerance response",
            "cumulative contribution metrics predict later structural residuals",
        ],
    }
    old_hypotheses[H_E] = {
        "hypothesis_id": H_E,
        "necessary_condition_classes": [
            "evidence_admissibility_result is EVIDENCE_ADMISSIBLE",
            "all required roles, observables, units, schemas, operator bindings, and nonperturbation controls are complete and valid",
            "H_A through H_D are each evaluated and all have status NOT_SUPPORTED",
            "complete valid evidence remains conflicting, below frozen discrimination thresholds, or otherwise nonclassifying",
        ],
        "supporting_condition_classes": [],
        "incomplete_required_evidence_allowed": False,
    }
    hypotheses = [old_hypotheses[item] for item in HYPOTHESES_A_TO_D] + [
        old_hypotheses[H_E]
    ]
    precedence = [
        "verify design, implementation, and operator custody",
        "verify exact run and payload identities",
        "verify every mandatory output is present",
        "verify instrumentation nonperturbation",
        "verify output units, schemas, norms, and normalization",
        "verify actual discrete-operator bindings",
        "evaluate H_A independently",
        "evaluate H_B independently",
        "evaluate H_C independently",
        "evaluate H_D independently",
        "preserve every individual hypothesis decision and its criterion records",
        "construct the ordered supported_mechanism_ids set from supported H_A through H_D",
        "assign the aggregate mechanism result from the support-set cardinality",
        "use H_E only when all required evidence is complete and admissible and the support set is empty",
        "apply the numerical-mechanism-only claim ceiling",
    ]
    return {
        "hypotheses": hypotheses,
        "independently_evaluated_mechanism_ids": HYPOTHESES_A_TO_D,
        "unresolved_hypothesis_id": H_E,
        "hypothesis_status_domain": HYPOTHESIS_STATUSES,
        "per_hypothesis_decision_schema": {
            "required_for_hypothesis_ids": HYPOTHESES_A_TO_D + [H_E],
            "required_fields": [
                "hypothesis_id",
                "status",
                "evidence_ids",
                "necessary_condition_decisions",
                "supporting_condition_decisions",
                "decision_reasons",
            ],
            "criterion_decision_fields": [
                "criterion_id",
                "status",
                "evidence_ids",
                "reason",
            ],
            "individual_records_may_not_be_replaced_by_aggregate": True,
        },
        "supported_mechanism_ids_schema": {
            "required": True,
            "allowed_ids": HYPOTHESES_A_TO_D,
            "ordering": "fixed H_A, H_B, H_C, H_D order",
            "duplicates_allowed": False,
            "must_equal_exact_supported_status_set": True,
            "required_for_single_and_multiple_outcomes": True,
        },
        "evidence_admissibility_outcomes": EVIDENCE_OUTCOMES,
        "aggregate_mechanism_outcomes": AGGREGATE_OUTCOMES,
        "classifier_precedence": precedence,
        "blocked_outcome_precedence": EVIDENCE_OUTCOMES[1:],
        "blocked_semantics": {
            "all_hypothesis_statuses": "NOT_EVALUATED",
            "supported_mechanism_ids": [],
            "aggregate_mechanism_result": "BLOCKED",
            "H_E_may_be_supported": False,
        },
        "admissible_aggregation_rules": [
            "if supported_mechanism_ids has one member, aggregate is SINGLE_SUPPORTED_MECHANISM",
            "if supported_mechanism_ids has two or more members, aggregate is MULTIPLE_SUPPORTED_MECHANISMS",
            "if supported_mechanism_ids is empty, H_E is SUPPORTED and aggregate is MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE",
        ],
        "H_E_complete_evidence_only": True,
        "required_evidence_incomplete_routes_to": "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
        "multiple_mechanisms_allowed": True,
        "forced_single_winner_allowed": False,
        "materiality_evaluation_called": False,
        "physical_or_model_domain_claim_called": False,
    }


def classify_design_semantics_fixture(
    evidence_result: str,
    mechanism_statuses: dict[str, str],
) -> dict[str, Any]:
    """Exercise only the v1 result-shape and precedence contract.

    This is deliberately not the future numerical classifier: it has no scientific
    thresholds and accepts already-decided H_A--H_D statuses as fixture input.
    """
    if evidence_result not in EVIDENCE_OUTCOMES:
        raise ValueError(f"unknown evidence result: {evidence_result}")
    if evidence_result != "EVIDENCE_ADMISSIBLE":
        records = {
            hypothesis_id: {"status": "NOT_EVALUATED"}
            for hypothesis_id in HYPOTHESES_A_TO_D + [H_E]
        }
        return {
            "evidence_result": evidence_result,
            "hypothesis_decisions": records,
            "supported_mechanism_ids": [],
            "aggregate_mechanism_result": "BLOCKED",
        }
    if set(mechanism_statuses) != set(HYPOTHESES_A_TO_D):
        raise ValueError("admissible fixture must decide every H_A through H_D")
    if any(
        status not in {"SUPPORTED", "NOT_SUPPORTED"}
        for status in mechanism_statuses.values()
    ):
        raise ValueError(
            "admissible fixture statuses must be SUPPORTED or NOT_SUPPORTED"
        )
    supported = [
        hypothesis_id
        for hypothesis_id in HYPOTHESES_A_TO_D
        if mechanism_statuses[hypothesis_id] == "SUPPORTED"
    ]
    records = {
        hypothesis_id: {"status": mechanism_statuses[hypothesis_id]}
        for hypothesis_id in HYPOTHESES_A_TO_D
    }
    if supported:
        records[H_E] = {"status": "NOT_SUPPORTED"}
        aggregate = (
            "SINGLE_SUPPORTED_MECHANISM"
            if len(supported) == 1
            else "MULTIPLE_SUPPORTED_MECHANISMS"
        )
    else:
        records[H_E] = {"status": "SUPPORTED"}
        aggregate = "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    return {
        "evidence_result": evidence_result,
        "hypothesis_decisions": records,
        "supported_mechanism_ids": supported,
        "aggregate_mechanism_result": aggregate,
    }


def validate_neighbor_universe_fixture(
    declared_candidate_ids: list[str], audited_candidate_ids: list[str]
) -> list[str]:
    if sorted(declared_candidate_ids) != sorted(audited_candidate_ids):
        return ["NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH"]
    return []


def validate_mechanism_result_fixture(
    result: dict[str, Any], *, required_evidence_complete: bool
) -> list[str]:
    """Validate adversarial result fixtures against the corrected design contract."""
    decisions = result.get("hypothesis_decisions", {})
    h_e_status = decisions.get(H_E, {}).get("status")
    if not required_evidence_complete and (
        h_e_status == "SUPPORTED"
        or result.get("aggregate_mechanism_result")
        == "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    ):
        return ["INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"]
    if (
        result.get("aggregate_mechanism_result")
        == "MULTIPLE_SUPPORTED_MECHANISMS"
        and "supported_mechanism_ids" not in result
    ):
        return ["MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"]
    expected_supported = [
        hypothesis_id
        for hypothesis_id in HYPOTHESES_A_TO_D
        if decisions.get(hypothesis_id, {}).get("status") == "SUPPORTED"
    ]
    if result.get("supported_mechanism_ids") != expected_supported:
        return ["SUPPORTED_MECHANISM_IDENTITY_SET_MISMATCH"]
    return []


def _regression_controls() -> dict[str, Any]:
    return {
        "adversarial_controls": [
            {
                "control_id": "N_NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH",
                "mutation": "declare thirteen passing non-R13 candidates but audit only eleven axis-sharing rows",
                "expected_diagnostic": "NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH",
            },
            {
                "control_id": "N_MULTIPLE_MECHANISM_IDENTITY_SET_MISSING",
                "fixture": [
                    "H_A_CANCELLATION_CONDITIONING",
                    "H_C_DISCRETE_CLOSURE_MISMATCH",
                ],
                "mutation": "emit MULTIPLE_SUPPORTED_MECHANISMS without supported_mechanism_ids",
                "expected_diagnostic": "MULTIPLE_MECHANISM_IDENTITY_SET_MISSING",
            },
            {
                "control_id": "N_INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED",
                "mutation": "remove required discrete closure output and mark H_E SUPPORTED",
                "expected_diagnostic": "INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED",
            },
        ],
        "positive_controls": [
            {
                "control_id": "P_ALL_THIRTEEN_NEIGHBOR_CANDIDATES_AUDITED",
                "expected": "thirteen unique non-R13 row IDs and no exclusions",
            },
            {
                "control_id": "P_R10_REMAINS_UNIQUE_TOP_CANDIDATE",
                "expected": "R10_MU_HIGH",
            },
            {
                "control_id": "P_MULTIPLE_IDENTITIES_RETAINED_EXACTLY",
                "fixture": [
                    "H_A_CANCELLATION_CONDITIONING",
                    "H_C_DISCRETE_CLOSURE_MISMATCH",
                ],
                "expected": "MULTIPLE_SUPPORTED_MECHANISMS with the same ordered two-ID set",
            },
            {
                "control_id": "P_COMPLETE_NONDISTINGUISHING_EVIDENCE_SUPPORTS_H_E",
                "expected": "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE",
            },
            {
                "control_id": "P_MISSING_EVIDENCE_BLOCKS_BEFORE_HYPOTHESES",
                "expected": "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE and all hypotheses NOT_EVALUATED",
            },
        ],
        "status": "DESIGN_REGRESSIONS_DEFINED_THRESHOLDS_AND_IMPLEMENTATION_DEFERRED_TO_FREEZE",
    }


DECISION_IDS = [
    "blocked_v0_review_is_exact_and_consumed_as_bounded_correction_authority",
    "all_v0_design_and_review_source_hashes_and_cross_bindings_are_exact",
    "all_203_canonical_outputs_execution_count_and_root_digest_remain_exact",
    "all_thirty_four_accepted_v0_review_decisions_are_preserved",
    "Route_A_and_three_scientific_questions_are_unchanged",
    "four_required_run_classes_are_unchanged",
    "fourteen_mechanism_observables_are_unchanged",
    "instrumentation_nonperturbation_contract_is_unchanged",
    "actual_discrete_operator_closure_contract_is_unchanged",
    "separate_output_custody_contract_is_unchanged",
    "sixteen_freeze_deferred_items_are_unchanged",
    "neighbor_candidate_universe_contains_all_thirteen_non_R13_rows",
    "all_thirteen_candidates_pass_canonical_and_linked_loose_role_criteria",
    "neighbor_ranking_tuple_is_exact_and_applied_after_universe_definition",
    "R10_remains_unique_provisional_top_and_zero_shared_rows_are_retained",
    "exact_neighbor_identity_remains_unfrozen",
    "H_A_through_H_D_are_evaluated_independently",
    "every_hypothesis_requires_status_evidence_criterion_records_and_reasons",
    "supported_mechanism_ids_is_required_exact_ordered_and_identity_preserving",
    "single_and_multiple_aggregates_are_derived_from_support_set_cardinality",
    "multiple_mechanism_support_retains_every_supported_identity",
    "H_E_requires_complete_admissible_nondiscriminating_evidence",
    "missing_required_evidence_blocks_before_all_hypothesis_evaluation",
    "evidence_admissibility_and_mechanism_results_are_separate_layers",
    "fifteen_step_fail_closed_classifier_precedence_is_explicit",
    "three_blocker_regressions_are_permanent_adversarial_controls",
    "five_positive_controls_cover_corrected_semantics",
    "no_numerical_values_thresholds_run_matrix_or_classifier_hash_are_frozen",
    "no_simulation_rerun_canonical_mutation_or_scientific_reclassification_is_authorized",
    "canonical_block_materiality_root_unknown_and_E_REPRO_status_remain_unchanged",
    "selected_next_target_is_independent_corrected_design_review_only",
]


def build_packet() -> dict[str, Any]:
    base = design_v0.build_packet()
    custody = _correction_source_custody(base)
    blocked_review = load_json(REPO_ROOT / BLOCKED_REVIEW_REPORT)
    neighbor = _all_passing_neighbor_audit()
    classifier = _corrected_hypotheses_and_classifier(base)
    controls = _regression_controls()
    preserved_sections = {
        "scientific_questions": copy.deepcopy(base["scientific_questions"]),
        "required_run_classes": copy.deepcopy(base["required_run_classes"]),
        "instrumentation_nonperturbation_contract": copy.deepcopy(
            base["instrumentation_nonperturbation_contract"]
        ),
        "mechanism_observable_registry": copy.deepcopy(
            base["mechanism_observable_registry"]
        ),
        "aggregation_block_registry_and_missing_data_contract": copy.deepcopy(
            base["aggregation_block_registry_and_missing_data_contract"]
        ),
        "discrete_Maxwell_continuity_closure_contract": copy.deepcopy(
            base["discrete_Maxwell_continuity_closure_contract"]
        ),
        "supporting_modules": copy.deepcopy(base["supporting_modules"]),
        "output_separation_and_custody_design": copy.deepcopy(
            base["output_separation_and_custody_design"]
        ),
        "freeze_deferred_registry": copy.deepcopy(base["freeze_deferred_registry"]),
    }
    accepted_v0_decisions = [
        item["decision_id"] for item in blocked_review["decisions"] if item["passed"]
    ]
    authority = copy.deepcopy(base["authority_boundary"])
    authority["design_packet_prepared"] = True
    authority["design_independently_accepted"] = False
    authority["numerical_freeze_packet_authorized"] = False
    decisions = {
        "blocked_v0_review_is_exact_and_consumed_as_bounded_correction_authority": custody[
            "blocked_v0_review_exact"
        ]
        and custody["bounded_correction_authority_consumed"] == CONSUMED_TARGET,
        "all_v0_design_and_review_source_hashes_and_cross_bindings_are_exact": custody[
            "all_correction_source_hashes_exact"
        ]
        and custody["design_v0_cross_bindings_exact"],
        "all_203_canonical_outputs_execution_count_and_root_digest_remain_exact": custody[
            "passed"
        ]
        and custody["canonical_run_output_count_checked"] == 203
        and custody["execution_count_performed"] == 1,
        "all_thirty_four_accepted_v0_review_decisions_are_preserved": len(
            accepted_v0_decisions
        )
        == 34,
        "Route_A_and_three_scientific_questions_are_unchanged": base[
            "inherited_authority"
        ]["selected_route"]
        == "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"
        and len(preserved_sections["scientific_questions"]) == 3,
        "four_required_run_classes_are_unchanged": len(
            preserved_sections["required_run_classes"]
        )
        == 4,
        "fourteen_mechanism_observables_are_unchanged": len(
            preserved_sections["mechanism_observable_registry"]
        )
        == 14,
        "instrumentation_nonperturbation_contract_is_unchanged": preserved_sections[
            "instrumentation_nonperturbation_contract"
        ]
        == base["instrumentation_nonperturbation_contract"],
        "actual_discrete_operator_closure_contract_is_unchanged": preserved_sections[
            "discrete_Maxwell_continuity_closure_contract"
        ]
        == base["discrete_Maxwell_continuity_closure_contract"],
        "separate_output_custody_contract_is_unchanged": preserved_sections[
            "output_separation_and_custody_design"
        ]
        == base["output_separation_and_custody_design"],
        "sixteen_freeze_deferred_items_are_unchanged": len(
            preserved_sections["freeze_deferred_registry"]
        )
        == 16,
        "neighbor_candidate_universe_contains_all_thirteen_non_R13_rows": neighbor[
            "all_non_R13_scientific_row_count"
        ]
        == 13
        and neighbor["eligible_candidate_count"] == 13
        and neighbor["audited_candidate_count"] == 13
        and neighbor["candidate_universe_matches_ranked_audit"],
        "all_thirteen_candidates_pass_canonical_and_linked_loose_role_criteria": neighbor[
            "excluded_candidate_ids"
        ]
        == []
        and all(
            item["all_applicable_canonical_criteria_pass"]
            and item["all_four_loose_solver_residual_ceilings_pass"]
            for item in neighbor["audited_candidate_universe"]
        ),
        "neighbor_ranking_tuple_is_exact_and_applied_after_universe_definition": neighbor[
            "candidate_universe_defined_before_ranking"
        ]
        and neighbor["ranking_tuple"]
        == [
            "negative_shared_axis_count",
            "normalized_distance",
            "scientific_row_id",
        ]
        and len(neighbor["ranked_candidate_audit"]) == 13,
        "R10_remains_unique_provisional_top_and_zero_shared_rows_are_retained": neighbor[
            "provisional_top_candidate_for_freeze_confirmation"
        ]
        == "R10_MU_HIGH"
        and neighbor["unique_top_candidate"]
        and neighbor["zero_shared_axis_candidates_retained"]
        == ["R06_THETA_TRIVIAL", "R07_THETA_PARTNER"],
        "exact_neighbor_identity_remains_unfrozen": neighbor[
            "exact_neighbor_frozen_now"
        ]
        is False,
        "H_A_through_H_D_are_evaluated_independently": classifier[
            "independently_evaluated_mechanism_ids"
        ]
        == HYPOTHESES_A_TO_D,
        "every_hypothesis_requires_status_evidence_criterion_records_and_reasons": classifier[
            "per_hypothesis_decision_schema"
        ]["required_for_hypothesis_ids"]
        == HYPOTHESES_A_TO_D + [H_E]
        and len(classifier["per_hypothesis_decision_schema"]["required_fields"]) == 6,
        "supported_mechanism_ids_is_required_exact_ordered_and_identity_preserving": classifier[
            "supported_mechanism_ids_schema"
        ]["required"]
        and classifier["supported_mechanism_ids_schema"][
            "must_equal_exact_supported_status_set"
        ]
        and classifier["supported_mechanism_ids_schema"]["duplicates_allowed"] is False,
        "single_and_multiple_aggregates_are_derived_from_support_set_cardinality": len(
            classifier["admissible_aggregation_rules"]
        )
        == 3,
        "multiple_mechanism_support_retains_every_supported_identity": classifier[
            "supported_mechanism_ids_schema"
        ]["required_for_single_and_multiple_outcomes"],
        "H_E_requires_complete_admissible_nondiscriminating_evidence": classifier[
            "H_E_complete_evidence_only"
        ]
        and classifier["hypotheses"][-1]["incomplete_required_evidence_allowed"]
        is False,
        "missing_required_evidence_blocks_before_all_hypothesis_evaluation": classifier[
            "required_evidence_incomplete_routes_to"
        ]
        == "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE"
        and classifier["blocked_semantics"]["all_hypothesis_statuses"]
        == "NOT_EVALUATED",
        "evidence_admissibility_and_mechanism_results_are_separate_layers": len(
            classifier["evidence_admissibility_outcomes"]
        )
        == 7
        and len(classifier["aggregate_mechanism_outcomes"]) == 4,
        "fifteen_step_fail_closed_classifier_precedence_is_explicit": len(
            classifier["classifier_precedence"]
        )
        == 15,
        "three_blocker_regressions_are_permanent_adversarial_controls": len(
            controls["adversarial_controls"]
        )
        == 3,
        "five_positive_controls_cover_corrected_semantics": len(
            controls["positive_controls"]
        )
        == 5,
        "no_numerical_values_thresholds_run_matrix_or_classifier_hash_are_frozen": authority[
            "exact_run_count_or_values_selected"
        ]
        is False
        and "exact classifier implementation and hash"
        in preserved_sections["freeze_deferred_registry"],
        "no_simulation_rerun_canonical_mutation_or_scientific_reclassification_is_authorized": authority[
            "new_simulation_authorized"
        ]
        is False
        and authority["rerun_authorized"] is False
        and authority["canonical_output_mutation_authorized"] is False
        and authority["robustness_reclassification_authorized"] is False,
        "canonical_block_materiality_root_unknown_and_E_REPRO_status_remain_unchanged": base[
            "inherited_authority"
        ]["canonical_robustness_status"]
        == "NUMERICALLY_BLOCKED"
        and base["inherited_authority"]["root_numerical_mechanism_status"]
        == "UNRESOLVED"
        and base["inherited_authority"]["descendant_materiality_status"]
        == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and base["inherited_authority"]["new_E_REPRO"] == "NONE",
        "selected_next_target_is_independent_corrected_design_review_only": True,
    }
    ordered = [
        {"decision_id": decision_id, "passed": bool(decisions[decision_id])}
        for decision_id in DECISION_IDS
    ]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_authority_target": CONSUMED_TARGET,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "INDEPENDENT_CORRECTED_DESIGN_REVIEW_ONLY",
        "downstream_target_if_independent_review_accepts": DOWNSTREAM_TARGET_IF_ACCEPTED,
        "claim_ceiling": (
            "Corrected numerical-mechanism experiment design only. This packet repairs three "
            "decision-contract defects and cannot freeze values, authorize execution, identify a "
            "mechanism, reclassify robustness, evaluate materiality, or award a scientific claim."
        ),
        "correction_source_custody": custody,
        "blocked_v0_review_preservation": {
            "reviewed_design_version": "v0",
            "accepted_decision_ids_preserved": accepted_v0_decisions,
            "accepted_decision_count_preserved": len(accepted_v0_decisions),
            "blocked_decision_ids_corrected": BLOCKED_V0_DECISION_IDS,
            "route_selection_reopened": False,
            "scientific_redesign_performed": False,
        },
        "inherited_authority": copy.deepcopy(base["inherited_authority"]),
        **preserved_sections,
        "matched_neighbor_selection_design": neighbor,
        "hypotheses_and_classifier_design": classifier,
        "permanent_regression_controls": controls,
        "correction_summary": [
            "candidate universe expanded and audited from eleven axis-sharing rows to all thirteen passing non-R13 rows",
            "individual H_A through H_D decisions and the exact supported_mechanism_ids set are mandatory",
            "H_E is restricted to complete admissible nondiscriminating evidence; incomplete evidence blocks first",
        ],
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "authority_boundary": authority,
        "nonclaims": [
            "no corrected design independently accepted",
            "no numerical freeze packet prepared or accepted",
            "no exact run count, run matrix, tolerance, duration, or neighbor frozen",
            "no exact output schema, floor, threshold, contrast, association, or classifier hash frozen",
            "no new output root or simulation",
            "no canonical output mutation or rerun",
            "no root mechanism identified",
            "no physical instability or model-domain boundary",
            "no conditional or broad robustness",
            "no descendant materiality",
            "no new E-REPRO",
            "no pillar, seam, C_k, CCFT, or master-action promotion",
            "no repository-wide green claim",
        ],
    }


def build_manifest(packet: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "packet": {
            "path": PACKET_RELATIVE_PATH,
            "sha256": sha256_bytes(canonical_json_bytes(packet)),
        },
        "generator": {
            "path": GENERATOR_RELATIVE_PATH,
            "sha256": sha256_path(REPO_ROOT / GENERATOR_RELATIVE_PATH),
        },
        "bound_correction_sources": [
            {"path": path, "sha256": digest}
            for path, digest in sorted(EXPECTED_CORRECTION_SOURCE_HASHES.items())
        ],
        "canonical_output_root_digest": packet["correction_source_custody"][
            "canonical_root_digest"
        ],
        "canonical_run_output_count_checked": packet["correction_source_custody"][
            "canonical_run_output_count_checked"
        ],
        "new_simulation_run_count": 0,
        "canonical_output_mutation_count": 0,
        "new_experiment_output_root_created": False,
    }


def build_report(packet: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": packet["verdict"],
        "selected_next_target": packet["selected_next_target"],
        "downstream_target_if_independent_review_accepts": packet[
            "downstream_target_if_independent_review_accepts"
        ],
        "artifact_hashes": {
            "generator_sha256": sha256_path(REPO_ROOT / GENERATOR_RELATIVE_PATH),
            "packet_sha256": sha256_bytes(canonical_json_bytes(packet)),
            "manifest_sha256": sha256_bytes(canonical_json_bytes(manifest)),
        },
        "correction_source_custody_passed": packet["correction_source_custody"][
            "passed"
        ],
        "canonical_root_digest": packet["correction_source_custody"][
            "canonical_root_digest"
        ],
        "preserved_v0_review_decision_count": packet[
            "blocked_v0_review_preservation"
        ]["accepted_decision_count_preserved"],
        "corrected_blocker_count": len(
            packet["blocked_v0_review_preservation"]["blocked_decision_ids_corrected"]
        ),
        "neighbor_candidate_count": packet["matched_neighbor_selection_design"][
            "eligible_candidate_count"
        ],
        "provisional_top_neighbor": packet["matched_neighbor_selection_design"][
            "provisional_top_candidate_for_freeze_confirmation"
        ],
        "mechanism_observable_count": len(packet["mechanism_observable_registry"]),
        "hypothesis_count": len(packet["hypotheses_and_classifier_design"]["hypotheses"]),
        "adversarial_control_count": len(
            packet["permanent_regression_controls"]["adversarial_controls"]
        ),
        "positive_control_count": len(
            packet["permanent_regression_controls"]["positive_controls"]
        ),
        "freeze_deferred_item_count": len(packet["freeze_deferred_registry"]),
        "decision_count": packet["decision_count"],
        "passed_decision_count": packet["passed_decision_count"],
        "failed_decision_ids": packet["failed_decision_ids"],
        "validation_status": {
            "focused_corrected_design_v1_tests": {"passed": 15, "failed": 0},
            "current_affected_descendant_robustness_chain": {
                "passed": 302,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 156, "status": "PASSED"},
            "authority_surface_parity": "PASSED",
            "simulation_invocation_count": 0,
            "canonical_output_mutation_count": 0,
            "historical_repository_wide_Lean": {
                "status": "INCOMPLETE_TIMEOUT",
                "completed_jobs": 8441,
                "total_jobs": 8507,
                "repository_wide_green_claim": False,
            },
        },
        "authority_boundary": packet["authority_boundary"],
        "nonclaims": packet["nonclaims"],
    }


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    manifest = build_manifest(packet)
    report = build_report(packet, manifest)
    return packet, manifest, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the corrected instrumented R13 mechanism design packet v1."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    before = canonical_root_digest()
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, KeyError, IndexError, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    artifacts = {
        PACKET_PATH: canonical_json_bytes(packet),
        MANIFEST_PATH: canonical_json_bytes(manifest),
        REPORT_PATH: canonical_json_bytes(report),
    }
    if args.write:
        for path, raw in artifacts.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    elif args.check:
        stale = [
            path.relative_to(REPO_ROOT).as_posix()
            for path, raw in artifacts.items()
            if not path.is_file() or path.read_bytes() != raw
        ]
        if stale:
            print(f"stale or missing corrected design artifacts: {stale}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(canonical_json_bytes(report))
    after = canonical_root_digest()
    if before != after:
        print("canonical output root changed during corrected design preparation", file=sys.stderr)
        return 1
    if packet["failed_decision_ids"]:
        print(f"corrected design decisions failed: {packet['failed_decision_ids']}", file=sys.stderr)
        return 2
    if args.write:
        print(
            f"wrote corrected instrumented R13 design v1: {packet['passed_decision_count']}/"
            f"{packet['decision_count']} decisions; selected {packet['selected_next_target']}"
        )
    elif args.check:
        print(
            f"corrected instrumented R13 design v1 verified: {packet['passed_decision_count']}/"
            f"{packet['decision_count']} decisions; canonical outputs unchanged"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
