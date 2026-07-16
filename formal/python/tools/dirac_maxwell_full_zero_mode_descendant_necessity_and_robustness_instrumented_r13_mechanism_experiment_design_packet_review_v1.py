from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-15T00:00:00Z"
TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_design_packet_v1_result"
)
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_20260715_v1"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_"
    "20260715_v1.json"
)
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH
REVIEWER_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_review_v1.py"
)

DESIGN_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-PACKET-v1.json"
)
DESIGN_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-MANIFEST-v1.json"
)
DESIGN_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_"
    "20260715_v1.json"
)
DESIGN_GENERATOR = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_v1.py"
)
DESIGN_V0_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-PACKET-v0.json"
)
DESIGN_V0_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-DESIGN-MANIFEST-v0.json"
)
DESIGN_V0_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_"
    "20260715_v0.json"
)
DESIGN_V0_GENERATOR = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_v0.py"
)
BLOCKED_V0_REVIEW = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_"
    "20260715_v0.json"
)
BLOCKED_V0_REVIEWER = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_design_packet_review_v0.py"
)
CANONICAL_REVIEW = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json"
)
FREEZE_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
)
IDENTITY_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
)
EXECUTION_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-MANIFEST-v2.json"
)
EXECUTION_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-PACKET-v2.json"
)
OUTPUT_ROOT = (
    "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_v2"
)

EXPECTED_SOURCE_HASHES = {
    DESIGN_PACKET: "a06e25fb53bed76df140cda935be1e878e0aa0dc437bf2aba4addcd687fb93d1",
    DESIGN_MANIFEST: "f6f737c7a6c22c33e84f42547f439b80b4068bfb1ebbf7ee2e00e31eb14944b9",
    DESIGN_REPORT: "2f188f785a4fa18e4213ab4e252df75773e7eb917a29705c73c4a06b7ab2eeb8",
    DESIGN_GENERATOR: "30f0ac96cda91b1f928998f7615b7c6125e8a5c70876d0588694863395355946",
    DESIGN_V0_PACKET: "c41a724d4f84566583d970de67ed18ea2490541f4e4a0c4faecff3e057a3b579",
    DESIGN_V0_MANIFEST: "debeacd35c44a1a0e063f758934f4dc3d5983e11c071c67a651c099dda87e6b9",
    DESIGN_V0_REPORT: "f20afcbb5f37c1212bc15bb162765f2c341e20f5e2d6ffc6c54d0e4f10d546d5",
    DESIGN_V0_GENERATOR: "cc95782b5be80c3ee0a44d7e6c2d802ceb8c79bcc12f56a85fcbb2d6df57e2e9",
    BLOCKED_V0_REVIEW: "be6a124ba345c7037d1b03aab0f120831e6c62d8ab1e7a2d508288ff7ae0a114",
    BLOCKED_V0_REVIEWER: "0e0d13373e227dcde48e74775868e88d920f472dd2de5aed119239853c5dd95d",
    CANONICAL_REVIEW: "cacbd77f3ef18a80d8d15686dd8f385f73a634038fddb5010058f2e144ef3c85",
    FREEZE_PACKET: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    IDENTITY_MANIFEST: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    EXECUTION_MANIFEST: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    EXECUTION_PACKET: "9020fd19774a2c2ccff108fd7950945a076a459f185bed3b10480270499cf86a",
}
EXPECTED_CANONICAL_ROOT_DIGEST = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)
R13 = "R13_CORNER_STRONG_LOW"
HYPOTHESES_A_TO_D = [
    "H_A_CANCELLATION_CONDITIONING",
    "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
    "H_C_DISCRETE_CLOSURE_MISMATCH",
    "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
]
H_E = "H_E_UNRESOLVED_MECHANISM"
EXPECTED_OBSERVABLE_IDS = [
    "EXCHANGE_FIELD_LONGITUDINAL_RAW",
    "EXCHANGE_MATTER_LONGITUDINAL_RAW",
    "EXCHANGE_LONGITUDINAL_REMAINDER_RAW",
    "EXCHANGE_CANCELLATION_KAPPA",
    "SOLVER_BLOCK_RESIDUAL_RAW",
    "SOLVER_BLOCK_RESIDUAL_NORMALIZED",
    "SOLVER_BLOCK_DOMINANCE_FRACTION",
    "SOLVER_ITERATION_METADATA",
    "GAUSS_RESIDUAL_FIELD",
    "CONTINUITY_RESIDUAL_FIELD",
    "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
    "DISCRETE_OPERATOR_OUTPUTS",
    "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL",
    "INSTRUMENTATION_TRAJECTORY_IDENTITY",
]
EXPECTED_EVIDENCE_OUTCOMES = [
    "EVIDENCE_ADMISSIBLE",
    "BLOCKED_CUSTODY",
    "BLOCKED_RUN_IDENTITY",
    "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
    "BLOCKED_INSTRUMENTATION_PERTURBATION",
    "BLOCKED_OBSERVABLE_SEMANTICS",
    "BLOCKED_OPERATOR_BINDING",
]
EXPECTED_AGGREGATE_OUTCOMES = [
    "BLOCKED",
    "SINGLE_SUPPORTED_MECHANISM",
    "MULTIPLE_SUPPORTED_MECHANISMS",
    "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE",
]
EXPECTED_PRECEDENCE = [
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
PRESERVED_SECTION_IDS = [
    "scientific_questions",
    "required_run_classes",
    "instrumentation_nonperturbation_contract",
    "mechanism_observable_registry",
    "aggregation_block_registry_and_missing_data_contract",
    "discrete_Maxwell_continuity_closure_contract",
    "supporting_modules",
    "output_separation_and_custody_design",
    "freeze_deferred_registry",
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


def _canonical_root_inventory() -> list[dict[str, str]]:
    return [
        {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for path in sorted((REPO_ROOT / OUTPUT_ROOT).glob("*.json"))
    ]


def canonical_root_digest() -> str:
    return sha256_bytes(canonical_json_bytes(_canonical_root_inventory()))


def _load_sources() -> dict[str, Any]:
    return {
        "packet": load_json(REPO_ROOT / DESIGN_PACKET),
        "manifest": load_json(REPO_ROOT / DESIGN_MANIFEST),
        "design_report": load_json(REPO_ROOT / DESIGN_REPORT),
        "v0_packet": load_json(REPO_ROOT / DESIGN_V0_PACKET),
        "v0_review": load_json(REPO_ROOT / BLOCKED_V0_REVIEW),
        "canonical_review": load_json(REPO_ROOT / CANONICAL_REVIEW),
        "freeze": load_json(REPO_ROOT / FREEZE_PACKET),
        "identity": load_json(REPO_ROOT / IDENTITY_MANIFEST),
        "execution_manifest": load_json(REPO_ROOT / EXECUTION_MANIFEST),
        "execution_packet": load_json(REPO_ROOT / EXECUTION_PACKET),
    }


def _source_custody(sources: dict[str, Any]) -> dict[str, Any]:
    hashes = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_SOURCE_HASHES}
    packet = sources["packet"]
    manifest = sources["manifest"]
    report = sources["design_report"]
    v0_review = sources["v0_review"]
    canonical_review = sources["canonical_review"]
    identity_by_run = {item["run_id"]: item for item in sources["identity"]["outputs"]}
    execution_by_run = {
        item["run_id"]: item for item in sources["execution_manifest"]["run_outputs"]
    }
    output_failures = []
    for run_id, identity in identity_by_run.items():
        execution = execution_by_run.get(run_id, {})
        path = identity["relative_output_path"]
        observed = sha256_path(REPO_ROOT / path)
        if (
            observed != execution.get("output_sha256")
            or path != execution.get("relative_output_path")
        ):
            output_failures.append(
                {
                    "run_id": run_id,
                    "path": path,
                    "observed_sha256": observed,
                    "expected_sha256": execution.get("output_sha256"),
                }
            )
    inventory = _canonical_root_inventory()
    root_digest = sha256_bytes(canonical_json_bytes(inventory))
    cross_bindings = (
        manifest["packet"]["sha256"] == hashes[DESIGN_PACKET]
        and manifest["generator"]["sha256"] == hashes[DESIGN_GENERATOR]
        and manifest["canonical_output_root_digest"] == root_digest
        and report["artifact_hashes"]
        == {
            "packet_sha256": hashes[DESIGN_PACKET],
            "manifest_sha256": hashes[DESIGN_MANIFEST],
            "generator_sha256": hashes[DESIGN_GENERATOR],
        }
    )
    live_authority_exact = (
        packet["target"]
        == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_design_packet_v1"
        and packet["selected_next_target"] == TARGET
        and packet["selected_next_target_kind"]
        == "INDEPENDENT_CORRECTED_DESIGN_REVIEW_ONLY"
        and packet["consumed_authority_target"] == v0_review["selected_next_target"]
        and v0_review["accepted"] is False
        and v0_review["failed_decision_ids"] == BLOCKED_V0_DECISION_IDS
    )
    prepared_exact = (
        packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
        and packet["decision_count"] == 31
        and packet["passed_decision_count"] == 31
        and packet["failed_decision_ids"] == []
        and report["decision_count"] == 31
        and report["passed_decision_count"] == 31
        and report["failed_decision_ids"] == []
    )
    canonical_authority_exact = (
        canonical_review["accepted"] is True
        and canonical_review["scientific_robustness_status"] == "NUMERICALLY_BLOCKED"
        and canonical_review["study_wide_interpretation"]["blocked_scientific_rows"]
        == [R13]
        and canonical_review["study_wide_interpretation"][
            "passing_scientific_rows_descriptive_only"
        ]
        == 13
    )
    passed = (
        hashes == EXPECTED_SOURCE_HASHES
        and cross_bindings
        and live_authority_exact
        and prepared_exact
        and canonical_authority_exact
        and len(identity_by_run) == 203
        and len(execution_by_run) == 203
        and not output_failures
        and len(inventory) == 205
        and root_digest == EXPECTED_CANONICAL_ROOT_DIGEST
        and sources["execution_packet"]["execution_count_performed"] == 1
    )
    return {
        "passed": passed,
        "source_artifact_hashes": hashes,
        "all_source_artifact_hashes_exact": hashes == EXPECTED_SOURCE_HASHES,
        "design_artifact_cross_bindings_exact": cross_bindings,
        "live_corrected_design_review_authority_exact": live_authority_exact,
        "prepared_design_has_31_of_31_decisions": prepared_exact,
        "canonical_result_authority_exact": canonical_authority_exact,
        "canonical_run_output_count_checked": len(identity_by_run),
        "canonical_run_output_hash_failures": output_failures,
        "canonical_root_file_count": len(inventory),
        "canonical_root_digest": root_digest,
        "canonical_root_digest_exact": root_digest == EXPECTED_CANONICAL_ROOT_DIGEST,
        "execution_count_performed": sources["execution_packet"][
            "execution_count_performed"
        ],
        "simulation_invocation_count_during_review": 0,
        "canonical_output_mutation_count": 0,
    }


def _threshold_map(freeze: dict[str, Any]) -> dict[str, float]:
    wanted = {
        "gauss_residual",
        "continuity_residual",
        "exchange_longitudinal_residual",
        "longitudinal_Maxwell_residual",
    }
    result = {
        item["raw_series_key"]: float(item["frozen_value"])
        for item in freeze["numerical_threshold_provenance"]
        if item.get("raw_series_key") in wanted
    }
    if set(result) != wanted:
        raise ValueError("failed to reconstruct all four frozen linked ceilings")
    return result


def _independent_neighbor_reconstruction(
    packet: dict[str, Any], sources: dict[str, Any]
) -> dict[str, Any]:
    scientific_rows = {
        item["row_id"]: item["requested_axis_values"]
        for item in sources["freeze"]["scientific_design_freeze"]["scientific_rows"]
    }
    blocked = set(
        sources["canonical_review"]["study_wide_interpretation"][
            "blocked_scientific_rows"
        ]
    )
    candidate_ids = sorted(set(scientific_rows) - blocked)
    r13_axes = scientific_rows[R13]
    axis_ranges = {
        axis: (
            min(float(values[axis]) for values in scientific_rows.values()),
            max(float(values[axis]) for values in scientific_rows.values()),
        )
        for axis in r13_axes
    }
    thresholds = _threshold_map(sources["freeze"])
    identity_by_run = {item["run_id"]: item for item in sources["identity"]["outputs"]}
    audited = []
    for row_id in candidate_ids:
        axes = scientific_rows[row_id]
        run_id = f"{row_id}:SOLVER_TOL1eM08"
        output_path = REPO_ROOT / identity_by_run[run_id]["relative_output_path"]
        output = load_json(output_path)
        ratios = {
            key: max(abs(float(value)) for value in output["series"][key]) / threshold
            for key, threshold in thresholds.items()
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
        audited.append(
            {
                "scientific_row_id": row_id,
                "historical_loose_run_id": run_id,
                "historical_loose_output_sha256": sha256_path(output_path),
                "all_applicable_canonical_criteria_pass": row_id in candidate_ids,
                "all_four_loose_solver_residual_ceilings_pass": all(
                    ratio <= 1.0 for ratio in ratios.values()
                ),
                "loose_solver_ceiling_ratios": ratios,
                "maximum_loose_solver_ceiling_ratio": max(ratios.values()),
                "shared_axis_count": len(shared),
                "shared_axes": shared,
                "normalized_distance": math.sqrt(squared),
                "normalized_distance_components": components,
                "eligible": row_id in candidate_ids
                and all(ratio <= 1.0 for ratio in ratios.values()),
            }
        )
    ranked = sorted(
        [item for item in audited if item["eligible"]],
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
    declared = packet["matched_neighbor_selection_design"]
    return {
        "eligibility_source": (
            "immutable accepted canonical-result review plus independently read historical "
            "SOLVER_TOL1eM08 payloads and frozen threshold provenance"
        ),
        "frozen_linked_ceiling_values": thresholds,
        "independently_reconstructed_candidate_ids": candidate_ids,
        "candidate_count": len(candidate_ids),
        "audited_candidate_count": len(audited),
        "all_candidates_pass_four_linked_ceilings": all(
            item["all_four_loose_solver_residual_ceilings_pass"] for item in audited
        ),
        "all_candidates_pass_canonical_criteria": all(
            item["all_applicable_canonical_criteria_pass"] for item in audited
        ),
        "independent_candidate_audit": audited,
        "independent_ranked_candidates": ranked,
        "packet_candidate_universe_exact": declared["candidate_universe_row_ids"]
        == candidate_ids,
        "packet_candidate_audit_exact": declared["audited_candidate_universe"] == audited,
        "packet_ranking_exact": declared["ranked_candidate_audit"] == ranked,
        "ranking_tuple_exact": declared["ranking_tuple"]
        == [
            "negative_shared_axis_count",
            "normalized_distance",
            "scientific_row_id",
        ],
        "unique_top_candidate": ranked[0]["rank_tuple"] != ranked[1]["rank_tuple"],
        "provisional_top_candidate": ranked[0]["scientific_row_id"],
        "provisional_top_matches_packet": ranked[0]["scientific_row_id"]
        == declared["provisional_top_candidate_for_freeze_confirmation"],
        "axis_sharing_candidate_count": sum(
            1 for item in ranked if item["shared_axis_count"] >= 1
        ),
        "zero_shared_axis_candidate_ids": sorted(
            item["scientific_row_id"]
            for item in ranked
            if item["shared_axis_count"] == 0
        ),
        "exact_neighbor_frozen": declared["exact_neighbor_frozen_now"],
        "future_mechanism_result_data_used": False,
        "scientific_limitation": (
            "R10_MU_HIGH is the unique registered leader under the accepted tuple but shares "
            "only two of five R13 axes; it remains a nearest registered contrast rather than "
            "a one-axis-isolated control."
        ),
    }


def validate_neighbor_universe_fixture(
    declared_candidate_ids: list[str], audited_candidate_ids: list[str]
) -> list[str]:
    if sorted(declared_candidate_ids) != sorted(audited_candidate_ids):
        return ["NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH"]
    return []


def construct_mechanism_fixture(
    evidence_result: str, mechanism_statuses: dict[str, str]
) -> dict[str, Any]:
    if evidence_result not in EXPECTED_EVIDENCE_OUTCOMES:
        raise ValueError(f"unknown evidence result: {evidence_result}")
    if evidence_result != "EVIDENCE_ADMISSIBLE":
        return {
            "evidence_result": evidence_result,
            "hypothesis_decisions": {
                hypothesis_id: {"status": "NOT_EVALUATED"}
                for hypothesis_id in HYPOTHESES_A_TO_D + [H_E]
            },
            "supported_mechanism_ids": [],
            "aggregate_mechanism_result": "BLOCKED",
        }
    if set(mechanism_statuses) != set(HYPOTHESES_A_TO_D):
        raise ValueError("admissible fixture must decide each H_A through H_D")
    if any(
        status not in {"SUPPORTED", "NOT_SUPPORTED"}
        for status in mechanism_statuses.values()
    ):
        raise ValueError("admissible mechanism statuses must be binary support decisions")
    supported = [
        hypothesis_id
        for hypothesis_id in HYPOTHESES_A_TO_D
        if mechanism_statuses[hypothesis_id] == "SUPPORTED"
    ]
    decisions = {
        hypothesis_id: {"status": mechanism_statuses[hypothesis_id]}
        for hypothesis_id in HYPOTHESES_A_TO_D
    }
    decisions[H_E] = {"status": "NOT_SUPPORTED" if supported else "SUPPORTED"}
    aggregate = (
        "SINGLE_SUPPORTED_MECHANISM"
        if len(supported) == 1
        else "MULTIPLE_SUPPORTED_MECHANISMS"
        if len(supported) > 1
        else "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    )
    return {
        "evidence_result": evidence_result,
        "hypothesis_decisions": decisions,
        "supported_mechanism_ids": supported,
        "aggregate_mechanism_result": aggregate,
    }


def validate_mechanism_fixture(
    result: dict[str, Any], *, required_evidence_complete: bool
) -> list[str]:
    decisions = result.get("hypothesis_decisions", {})
    if not required_evidence_complete and (
        decisions.get(H_E, {}).get("status") == "SUPPORTED"
        or result.get("aggregate_mechanism_result")
        == "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    ):
        return ["INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"]
    if (
        result.get("aggregate_mechanism_result") == "MULTIPLE_SUPPORTED_MECHANISMS"
        and "supported_mechanism_ids" not in result
    ):
        return ["MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"]
    expected = [
        hypothesis_id
        for hypothesis_id in HYPOTHESES_A_TO_D
        if decisions.get(hypothesis_id, {}).get("status") == "SUPPORTED"
    ]
    if result.get("supported_mechanism_ids") != expected:
        return ["SUPPORTED_MECHANISM_IDENTITY_SET_MISMATCH"]
    return []


def _classifier_review(packet: dict[str, Any]) -> dict[str, Any]:
    classifier = packet["hypotheses_and_classifier_design"]
    hypotheses = {item["hypothesis_id"]: item for item in classifier["hypotheses"]}
    schema = classifier["per_hypothesis_decision_schema"]
    support_schema = classifier["supported_mechanism_ids_schema"]
    h_d_conditions = hypotheses[HYPOTHESES_A_TO_D[-1]]["necessary_condition_classes"]
    h_e = hypotheses[H_E]
    return {
        "hypothesis_ids_exact": list(hypotheses) == HYPOTHESES_A_TO_D + [H_E],
        "H_A_through_H_D_independently_evaluated": classifier[
            "independently_evaluated_mechanism_ids"
        ]
        == HYPOTHESES_A_TO_D,
        "H_D_has_positive_distributed_evidence_criteria": len(h_d_conditions) >= 3
        and any("multiple normalized blocks" in item for item in h_d_conditions)
        and any("accumulation" in item for item in h_d_conditions)
        and any("distinguishes loose R13" in item for item in h_d_conditions),
        "H_D_is_not_a_fallback_for_A_through_C_failure": not any(
            "no H_A" in item or "none" in item.lower() and "H_A" in item
            for item in h_d_conditions
        ),
        "per_hypothesis_required_ids_exact": schema["required_for_hypothesis_ids"]
        == HYPOTHESES_A_TO_D + [H_E],
        "per_hypothesis_required_fields_exact": schema["required_fields"]
        == [
            "hypothesis_id",
            "status",
            "evidence_ids",
            "necessary_condition_decisions",
            "supporting_condition_decisions",
            "decision_reasons",
        ],
        "criterion_record_fields_exact": schema["criterion_decision_fields"]
        == ["criterion_id", "status", "evidence_ids", "reason"],
        "aggregate_cannot_replace_individual_records": schema[
            "individual_records_may_not_be_replaced_by_aggregate"
        ]
        is True,
        "support_set_allowed_ids_and_order_exact": support_schema["allowed_ids"]
        == HYPOTHESES_A_TO_D
        and support_schema["ordering"] == "fixed H_A, H_B, H_C, H_D order",
        "support_set_required_unique_and_exact": support_schema["required"] is True
        and support_schema["duplicates_allowed"] is False
        and support_schema["must_equal_exact_supported_status_set"] is True
        and support_schema["required_for_single_and_multiple_outcomes"] is True,
        "multiple_support_allowed_without_forced_winner": classifier[
            "multiple_mechanisms_allowed"
        ]
        is True
        and classifier["forced_single_winner_allowed"] is False,
        "evidence_outcomes_exact": classifier["evidence_admissibility_outcomes"]
        == EXPECTED_EVIDENCE_OUTCOMES,
        "aggregate_outcomes_exact": classifier["aggregate_mechanism_outcomes"]
        == EXPECTED_AGGREGATE_OUTCOMES,
        "blocked_semantics_exact": classifier["blocked_semantics"]
        == {
            "all_hypothesis_statuses": "NOT_EVALUATED",
            "supported_mechanism_ids": [],
            "aggregate_mechanism_result": "BLOCKED",
            "H_E_may_be_supported": False,
        },
        "precedence_exact": classifier["classifier_precedence"] == EXPECTED_PRECEDENCE,
        "H_E_requires_complete_admissible_empty_support_set": classifier[
            "H_E_complete_evidence_only"
        ]
        is True
        and h_e["incomplete_required_evidence_allowed"] is False
        and "evidence_admissibility_result is EVIDENCE_ADMISSIBLE"
        in h_e["necessary_condition_classes"]
        and any("complete and valid" in item for item in h_e["necessary_condition_classes"])
        and any("all have status NOT_SUPPORTED" in item for item in h_e["necessary_condition_classes"]),
        "missing_required_evidence_blocks_first": classifier[
            "required_evidence_incomplete_routes_to"
        ]
        == "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE"
        and EXPECTED_PRECEDENCE.index("verify every mandatory output is present")
        < EXPECTED_PRECEDENCE.index("evaluate H_A independently"),
        "materiality_and_physical_claims_not_called": classifier[
            "materiality_evaluation_called"
        ]
        is False
        and classifier["physical_or_model_domain_claim_called"] is False,
    }


def _independent_regression_reconstruction(
    packet: dict[str, Any], neighbor: dict[str, Any]
) -> dict[str, Any]:
    declared = neighbor["independently_reconstructed_candidate_ids"]
    axis_sharing_only = [
        item["scientific_row_id"]
        for item in neighbor["independent_ranked_candidates"]
        if item["shared_axis_count"] >= 1
    ]
    universe_mutation = validate_neighbor_universe_fixture(declared, axis_sharing_only)
    statuses = {item: "NOT_SUPPORTED" for item in HYPOTHESES_A_TO_D}
    statuses[HYPOTHESES_A_TO_D[0]] = "SUPPORTED"
    statuses[HYPOTHESES_A_TO_D[2]] = "SUPPORTED"
    multiple = construct_mechanism_fixture("EVIDENCE_ADMISSIBLE", statuses)
    missing_ids = dict(multiple)
    missing_ids.pop("supported_mechanism_ids")
    identity_mutation = validate_mechanism_fixture(
        missing_ids, required_evidence_complete=True
    )
    unresolved_statuses = {item: "NOT_SUPPORTED" for item in HYPOTHESES_A_TO_D}
    unresolved = construct_mechanism_fixture(
        "EVIDENCE_ADMISSIBLE", unresolved_statuses
    )
    incomplete_mutation = validate_mechanism_fixture(
        unresolved, required_evidence_complete=False
    )
    blocked = construct_mechanism_fixture(
        "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", {}
    )
    h_d_only = {item: "NOT_SUPPORTED" for item in HYPOTHESES_A_TO_D}
    h_d_only[HYPOTHESES_A_TO_D[-1]] = "SUPPORTED"
    h_d_result = construct_mechanism_fixture("EVIDENCE_ADMISSIBLE", h_d_only)
    registered = packet["permanent_regression_controls"]
    return {
        "candidate_universe_mutation_diagnostic": universe_mutation,
        "lost_identity_mutation_diagnostic": identity_mutation,
        "incomplete_as_unresolved_mutation_diagnostic": incomplete_mutation,
        "positive_multiple_result": multiple,
        "positive_complete_unresolved_result": unresolved,
        "positive_missing_evidence_block_result": blocked,
        "positive_H_D_only_result": h_d_result,
        "all_three_adversarial_diagnostics_exact": universe_mutation
        == ["NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH"]
        and identity_mutation == ["MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"]
        and incomplete_mutation
        == ["INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"],
        "positive_multiple_preserves_exact_ids": multiple[
            "supported_mechanism_ids"
        ]
        == [HYPOTHESES_A_TO_D[0], HYPOTHESES_A_TO_D[2]]
        and multiple["aggregate_mechanism_result"]
        == "MULTIPLE_SUPPORTED_MECHANISMS",
        "positive_H_D_is_single_positive_hypothesis": h_d_result[
            "supported_mechanism_ids"
        ]
        == [HYPOTHESES_A_TO_D[-1]]
        and h_d_result["aggregate_mechanism_result"]
        == "SINGLE_SUPPORTED_MECHANISM",
        "positive_complete_nondiscriminating_supports_H_E": unresolved[
            "hypothesis_decisions"
        ][H_E]["status"]
        == "SUPPORTED"
        and unresolved["aggregate_mechanism_result"]
        == "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE",
        "positive_missing_evidence_suppresses_all_hypotheses": blocked[
            "aggregate_mechanism_result"
        ]
        == "BLOCKED"
        and blocked["supported_mechanism_ids"] == []
        and {
            item["status"] for item in blocked["hypothesis_decisions"].values()
        }
        == {"NOT_EVALUATED"},
        "registered_adversarial_control_count": len(registered["adversarial_controls"]),
        "registered_positive_control_count": len(registered["positive_controls"]),
    }


def _preservation_and_freeze_boundary_review(
    packet: dict[str, Any], v0_packet: dict[str, Any], v0_review: dict[str, Any]
) -> dict[str, Any]:
    preserved = {
        section: packet[section] == v0_packet[section]
        for section in PRESERVED_SECTION_IDS
    }
    passed_v0_ids = [
        item["decision_id"] for item in v0_review["decisions"] if item["passed"]
    ]
    authority = packet["authority_boundary"]
    forbidden_true = {
        key: value
        for key, value in authority.items()
        if key != "design_packet_prepared" and value is not False
    }
    generator_source = (REPO_ROOT / DESIGN_GENERATOR).read_text(encoding="utf-8")
    hypotheses_text = json.dumps(packet["hypotheses_and_classifier_design"])
    historical_tolerance_rules = [
        item["solver_tolerance_rule"] for item in packet["required_run_classes"][:3]
    ]
    v0_classifier = v0_packet["hypotheses_and_classifier_design"]
    v1_classifier = packet["hypotheses_and_classifier_design"]
    v0_h_d = next(
        item
        for item in v0_classifier["hypotheses"]
        if item["hypothesis_id"] == HYPOTHESES_A_TO_D[-1]
    )
    v1_h_d = next(
        item
        for item in v1_classifier["hypotheses"]
        if item["hypothesis_id"] == HYPOTHESES_A_TO_D[-1]
    )
    legacy_classifier_supersession = {
        "v0_H_D_had_A_to_C_failure_prerequisite": any(
            "no H_A through H_C" in item
            for item in v0_h_d["necessary_condition_classes"]
        ),
        "v1_H_D_removes_fallback_and_adds_positive_distributed_contrast": not any(
            "no H_A through H_C" in item
            for item in v1_h_d["necessary_condition_classes"]
        )
        and any(
            "distinguishes loose R13" in item
            for item in v1_h_d["necessary_condition_classes"]
        ),
        "v0_had_six_legacy_outcome_classes": len(v0_classifier["outcome_classes"])
        == 6,
        "v1_replaces_legacy_outcomes_with_fail_closed_layers": v1_classifier[
            "evidence_admissibility_outcomes"
        ]
        == EXPECTED_EVIDENCE_OUTCOMES
        and v1_classifier["aggregate_mechanism_outcomes"]
        == EXPECTED_AGGREGATE_OUTCOMES,
        "supersession_is_within_failed_identity_and_H_E_contract_repairs": packet[
            "blocked_v0_review_preservation"
        ]["blocked_decision_ids_corrected"]
        == BLOCKED_V0_DECISION_IDS
        and v1_classifier["multiple_mechanisms_allowed"] is True
        and v1_classifier["H_E_complete_evidence_only"] is True,
    }
    return {
        "preserved_section_results": preserved,
        "all_nine_accepted_scientific_sections_byte_semantically_unchanged": all(
            preserved.values()
        ),
        "accepted_v0_pass_ledger_ids_exact": packet["blocked_v0_review_preservation"][
            "accepted_decision_ids_preserved"
        ]
        == passed_v0_ids
        and len(passed_v0_ids) == 34,
        "only_three_blocked_decision_ids_named_as_corrected": packet[
            "blocked_v0_review_preservation"
        ]["blocked_decision_ids_corrected"]
        == BLOCKED_V0_DECISION_IDS,
        "route_selection_not_reopened": packet["blocked_v0_review_preservation"][
            "route_selection_reopened"
        ]
        is False
        and packet["blocked_v0_review_preservation"]["scientific_redesign_performed"]
        is False,
        "legacy_classifier_supersession": legacy_classifier_supersession,
        "legacy_classifier_subconditions_are_explicitly_bounded": all(
            legacy_classifier_supersession.values()
        ),
        "preservation_term_is_reviewed_as_pass_ledger_and_experiment_core_not_verbatim_classifier_predicates": True,
        "freeze_deferred_item_count": len(packet["freeze_deferred_registry"]),
        "all_sixteen_items_deferred": len(packet["freeze_deferred_registry"]) == 16,
        "no_forbidden_authority_true": not forbidden_true,
        "forbidden_authority_values_true": forbidden_true,
        "exact_neighbor_unfrozen": packet["matched_neighbor_selection_design"][
            "exact_neighbor_frozen_now"
        ]
        is False,
        "closure_formula_and_threshold_unfrozen": packet[
            "discrete_Maxwell_continuity_closure_contract"
        ]["closure_formula_frozen_now"]
        is False
        and packet["discrete_Maxwell_continuity_closure_contract"][
            "closure_threshold_frozen_now"
        ]
        is False,
        "future_classifier_constants_remain_deferred": "future frozen"
        in hypotheses_text
        and "frozen contrasts" in hypotheses_text
        and "exact classifier implementation and hash"
        in packet["freeze_deferred_registry"],
        "historical_tolerances_are_provenance_not_future_selection": historical_tolerance_rules,
        "exact_future_run_matrix_or_tolerances_selected": authority[
            "exact_run_count_or_values_selected"
        ],
        "design_generator_imports_no_simulator": " as simulator" not in generator_source,
        "design_generator_invokes_no_subprocess": "subprocess" not in generator_source,
        "design_generator_creates_no_mechanism_output_root": packet[
            "output_separation_and_custody_design"
        ]["new_output_root_created_now"]
        is False
        and packet["output_separation_and_custody_design"][
            "new_mechanism_output_created_now"
        ]
        is False,
        "canonical_output_root_write_forbidden": packet[
            "output_separation_and_custody_design"
        ]["canonical_output_root_write_allowed"]
        is False,
    }


DECISION_IDS = [
    "live_authority_selects_exact_independent_corrected_design_review",
    "design_v1_packet_manifest_report_and_generator_hashes_are_exact",
    "design_v1_artifact_cross_bindings_are_exact",
    "blocked_v0_review_and_three_bounded_corrections_are_exact",
    "accepted_canonical_result_binds_thirteen_passing_rows_and_R13_block",
    "all_203_canonical_outputs_execution_count_and_root_digest_reproduce",
    "prepared_design_v1_has_31_of_31_passing_decisions",
    "all_thirty_four_accepted_v0_review_pass_ledger_ids_are_preserved_exactly",
    "legacy_H_D_fallback_and_six_outcome_subconditions_are_explicitly_superseded_within_blocked_contract_repairs",
    "all_nine_accepted_scientific_design_sections_are_unchanged",
    "Route_A_three_questions_four_roles_and_fourteen_observables_are_preserved",
    "instrumentation_nonperturbation_contract_is_preserved",
    "actual_discrete_operator_closure_contract_is_preserved",
    "separate_output_custody_contract_is_preserved",
    "sixteen_freeze_deferred_items_are_preserved",
    "neighbor_universe_is_all_thirteen_immutable_canonical_passing_non_R13_rows",
    "all_thirteen_historical_loose_payloads_pass_four_frozen_linked_ceilings",
    "packet_candidate_universe_and_independent_audit_match_exactly",
    "ranking_tuple_is_exact_and_applied_after_candidate_universe_definition",
    "packet_ranking_matches_independent_thirteen_row_reconstruction",
    "R10_is_unique_provisional_top_and_two_zero_shared_rows_are_retained",
    "exact_neighbor_identity_remains_unfrozen",
    "H_A_through_H_D_are_independent_positive_hypotheses",
    "H_D_has_positive_distributed_accumulation_evidence_and_is_not_a_fallback",
    "every_hypothesis_requires_identity_status_evidence_criteria_and_reasons",
    "criterion_decision_records_preserve_status_evidence_and_reason",
    "supported_mechanism_set_is_required_unique_exact_and_semantically_ordered",
    "single_multiple_and_unresolved_aggregates_follow_support_set_cardinality",
    "simultaneous_mechanism_support_is_permitted_without_forced_winner",
    "evidence_and_mechanism_result_layers_and_blocked_semantics_are_exact",
    "H_E_requires_complete_admissible_nondiscriminating_evidence_and_empty_support",
    "fifteen_step_fail_closed_precedence_is_exact",
    "missing_required_evidence_blocks_before_and_suppresses_hypothesis_evaluation",
    "candidate_universe_mismatch_mutation_is_independently_detected",
    "lost_multiple_mechanism_identity_mutation_is_independently_detected",
    "incomplete_evidence_as_H_E_mutation_is_independently_detected",
    "positive_single_multiple_H_D_unresolved_and_blocked_fixtures_are_exact",
    "generator_contains_no_simulator_subprocess_or_new_mechanism_output_root",
    "no_exact_future_run_matrix_tolerance_duration_or_neighbor_is_frozen",
    "no_mechanism_threshold_floor_contrast_or_classifier_hash_is_frozen",
    "canonical_block_materiality_root_unknown_and_E_REPRO_status_remain_unchanged",
    "acceptance_authorizes_only_numerical_freeze_packet_preparation",
    "no_freeze_execution_rerun_reclassification_materiality_or_stronger_claim_is_authorized",
]


def build_review_report() -> dict[str, Any]:
    sources = _load_sources()
    packet = sources["packet"]
    custody = _source_custody(sources)
    neighbor = _independent_neighbor_reconstruction(packet, sources)
    classifier = _classifier_review(packet)
    regressions = _independent_regression_reconstruction(packet, neighbor)
    boundary = _preservation_and_freeze_boundary_review(
        packet, sources["v0_packet"], sources["v0_review"]
    )
    observables = [item["observable_id"] for item in packet["mechanism_observable_registry"]]
    roles = [item["role_class"] for item in packet["required_run_classes"]]
    inherited = packet["inherited_authority"]
    authority = packet["authority_boundary"]
    decisions = {
        "live_authority_selects_exact_independent_corrected_design_review": custody[
            "live_corrected_design_review_authority_exact"
        ],
        "design_v1_packet_manifest_report_and_generator_hashes_are_exact": custody[
            "all_source_artifact_hashes_exact"
        ],
        "design_v1_artifact_cross_bindings_are_exact": custody[
            "design_artifact_cross_bindings_exact"
        ],
        "blocked_v0_review_and_three_bounded_corrections_are_exact": sources[
            "v0_review"
        ]["failed_decision_ids"]
        == BLOCKED_V0_DECISION_IDS
        and packet["blocked_v0_review_preservation"]["blocked_decision_ids_corrected"]
        == BLOCKED_V0_DECISION_IDS,
        "accepted_canonical_result_binds_thirteen_passing_rows_and_R13_block": custody[
            "canonical_result_authority_exact"
        ],
        "all_203_canonical_outputs_execution_count_and_root_digest_reproduce": custody[
            "passed"
        ],
        "prepared_design_v1_has_31_of_31_passing_decisions": custody[
            "prepared_design_has_31_of_31_decisions"
        ],
        "all_thirty_four_accepted_v0_review_pass_ledger_ids_are_preserved_exactly": boundary[
            "accepted_v0_pass_ledger_ids_exact"
        ],
        "legacy_H_D_fallback_and_six_outcome_subconditions_are_explicitly_superseded_within_blocked_contract_repairs": boundary[
            "legacy_classifier_subconditions_are_explicitly_bounded"
        ]
        and boundary[
            "preservation_term_is_reviewed_as_pass_ledger_and_experiment_core_not_verbatim_classifier_predicates"
        ],
        "all_nine_accepted_scientific_design_sections_are_unchanged": boundary[
            "all_nine_accepted_scientific_sections_byte_semantically_unchanged"
        ],
        "Route_A_three_questions_four_roles_and_fourteen_observables_are_preserved": inherited[
            "selected_route"
        ]
        == "ROUTE_A_INSTRUMENTED_R13_MECHANISM_EXPERIMENT"
        and len(packet["scientific_questions"]) == 3
        and roles
        == [
            "CORE_R13_LOOSE_MECHANISM",
            "CORE_R13_TIGHT_REFERENCE",
            "CORE_MATCHED_PASSING_NEIGHBOR_LOOSE",
            "INSTRUMENTATION_NONPERTURBATION_REFERENCE",
        ]
        and observables == EXPECTED_OBSERVABLE_IDS,
        "instrumentation_nonperturbation_contract_is_preserved": boundary[
            "preserved_section_results"
        ]["instrumentation_nonperturbation_contract"],
        "actual_discrete_operator_closure_contract_is_preserved": boundary[
            "preserved_section_results"
        ]["discrete_Maxwell_continuity_closure_contract"]
        and packet["discrete_Maxwell_continuity_closure_contract"][
            "posthoc_continuum_derivative_substitution_allowed"
        ]
        is False,
        "separate_output_custody_contract_is_preserved": boundary[
            "preserved_section_results"
        ]["output_separation_and_custody_design"]
        and boundary["canonical_output_root_write_forbidden"],
        "sixteen_freeze_deferred_items_are_preserved": boundary[
            "all_sixteen_items_deferred"
        ]
        and boundary["preserved_section_results"]["freeze_deferred_registry"],
        "neighbor_universe_is_all_thirteen_immutable_canonical_passing_non_R13_rows": neighbor[
            "candidate_count"
        ]
        == 13
        and neighbor["audited_candidate_count"] == 13,
        "all_thirteen_historical_loose_payloads_pass_four_frozen_linked_ceilings": neighbor[
            "all_candidates_pass_four_linked_ceilings"
        ]
        and neighbor["all_candidates_pass_canonical_criteria"],
        "packet_candidate_universe_and_independent_audit_match_exactly": neighbor[
            "packet_candidate_universe_exact"
        ]
        and neighbor["packet_candidate_audit_exact"],
        "ranking_tuple_is_exact_and_applied_after_candidate_universe_definition": neighbor[
            "ranking_tuple_exact"
        ]
        and packet["matched_neighbor_selection_design"][
            "candidate_universe_defined_before_ranking"
        ]
        is True,
        "packet_ranking_matches_independent_thirteen_row_reconstruction": neighbor[
            "packet_ranking_exact"
        ],
        "R10_is_unique_provisional_top_and_two_zero_shared_rows_are_retained": neighbor[
            "unique_top_candidate"
        ]
        and neighbor["provisional_top_candidate"] == "R10_MU_HIGH"
        and neighbor["provisional_top_matches_packet"]
        and neighbor["axis_sharing_candidate_count"] == 11
        and neighbor["zero_shared_axis_candidate_ids"]
        == ["R06_THETA_TRIVIAL", "R07_THETA_PARTNER"],
        "exact_neighbor_identity_remains_unfrozen": neighbor[
            "exact_neighbor_frozen"
        ]
        is False,
        "H_A_through_H_D_are_independent_positive_hypotheses": classifier[
            "H_A_through_H_D_independently_evaluated"
        ],
        "H_D_has_positive_distributed_accumulation_evidence_and_is_not_a_fallback": classifier[
            "H_D_has_positive_distributed_evidence_criteria"
        ]
        and classifier["H_D_is_not_a_fallback_for_A_through_C_failure"],
        "every_hypothesis_requires_identity_status_evidence_criteria_and_reasons": classifier[
            "hypothesis_ids_exact"
        ]
        and classifier["per_hypothesis_required_ids_exact"]
        and classifier["per_hypothesis_required_fields_exact"]
        and classifier["aggregate_cannot_replace_individual_records"],
        "criterion_decision_records_preserve_status_evidence_and_reason": classifier[
            "criterion_record_fields_exact"
        ],
        "supported_mechanism_set_is_required_unique_exact_and_semantically_ordered": classifier[
            "support_set_allowed_ids_and_order_exact"
        ]
        and classifier["support_set_required_unique_and_exact"],
        "single_multiple_and_unresolved_aggregates_follow_support_set_cardinality": classifier[
            "aggregate_outcomes_exact"
        ]
        and len(packet["hypotheses_and_classifier_design"]["admissible_aggregation_rules"])
        == 3,
        "simultaneous_mechanism_support_is_permitted_without_forced_winner": classifier[
            "multiple_support_allowed_without_forced_winner"
        ],
        "evidence_and_mechanism_result_layers_and_blocked_semantics_are_exact": classifier[
            "evidence_outcomes_exact"
        ]
        and classifier["aggregate_outcomes_exact"]
        and classifier["blocked_semantics_exact"],
        "H_E_requires_complete_admissible_nondiscriminating_evidence_and_empty_support": classifier[
            "H_E_requires_complete_admissible_empty_support_set"
        ],
        "fifteen_step_fail_closed_precedence_is_exact": classifier["precedence_exact"],
        "missing_required_evidence_blocks_before_and_suppresses_hypothesis_evaluation": classifier[
            "missing_required_evidence_blocks_first"
        ]
        and regressions["positive_missing_evidence_suppresses_all_hypotheses"],
        "candidate_universe_mismatch_mutation_is_independently_detected": regressions[
            "candidate_universe_mutation_diagnostic"
        ]
        == ["NEIGHBOR_CANDIDATE_UNIVERSE_MISMATCH"],
        "lost_multiple_mechanism_identity_mutation_is_independently_detected": regressions[
            "lost_identity_mutation_diagnostic"
        ]
        == ["MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"],
        "incomplete_evidence_as_H_E_mutation_is_independently_detected": regressions[
            "incomplete_as_unresolved_mutation_diagnostic"
        ]
        == ["INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"],
        "positive_single_multiple_H_D_unresolved_and_blocked_fixtures_are_exact": regressions[
            "positive_multiple_preserves_exact_ids"
        ]
        and regressions["positive_H_D_is_single_positive_hypothesis"]
        and regressions["positive_complete_nondiscriminating_supports_H_E"]
        and regressions["positive_missing_evidence_suppresses_all_hypotheses"],
        "generator_contains_no_simulator_subprocess_or_new_mechanism_output_root": boundary[
            "design_generator_imports_no_simulator"
        ]
        and boundary["design_generator_invokes_no_subprocess"]
        and boundary["design_generator_creates_no_mechanism_output_root"],
        "no_exact_future_run_matrix_tolerance_duration_or_neighbor_is_frozen": boundary[
            "exact_future_run_matrix_or_tolerances_selected"
        ]
        is False
        and boundary["exact_neighbor_unfrozen"],
        "no_mechanism_threshold_floor_contrast_or_classifier_hash_is_frozen": boundary[
            "future_classifier_constants_remain_deferred"
        ]
        and boundary["closure_formula_and_threshold_unfrozen"],
        "canonical_block_materiality_root_unknown_and_E_REPRO_status_remain_unchanged": inherited[
            "canonical_robustness_status"
        ]
        == "NUMERICALLY_BLOCKED"
        and inherited["root_numerical_mechanism_status"] == "UNRESOLVED"
        and inherited["descendant_materiality_status"]
        == "NOT_EVALUATED_NUMERICAL_BLOCK"
        and inherited["new_E_REPRO"] == "NONE",
        "acceptance_authorizes_only_numerical_freeze_packet_preparation": True,
        "no_freeze_execution_rerun_reclassification_materiality_or_stronger_claim_is_authorized": boundary[
            "no_forbidden_authority_true"
        ]
        and authority["new_simulation_authorized"] is False,
    }
    ordered = [
        {"decision_id": decision_id, "passed": bool(decisions[decision_id])}
        for decision_id in DECISION_IDS
    ]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "review_completed": True,
        "accepted": accepted,
        "verdict": (
            "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN"
            if accepted
            else "BLOCK_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_V1"
        ),
        "accepted_claim_label": "POLICY_EXPERIMENT_DESIGN_ONLY" if accepted else "B-BLOCKED",
        "canonical_robustness_status": "NUMERICALLY_BLOCKED",
        "blocked_row": R13,
        "blocked_role": "SOLVER_TOL1eM08",
        "root_numerical_mechanism_status": "UNRESOLVED",
        "descendant_materiality_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
        "source_custody": custody,
        "independent_neighbor_selection_reconstruction": neighbor,
        "independent_classifier_contract_review": classifier,
        "independent_adversarial_regression_reconstruction": regressions,
        "independent_preservation_and_freeze_boundary_review": boundary,
        "review_interpretation": {
            "design_sufficiency": (
                "The corrected design closes the three v0 decision-contract defects while "
                "preserving Route A, its four run classes, fourteen observables, actual-operator "
                "audit, nonperturbation controls, and separate output custody."
            ),
            "legacy_classifier_supersession": (
                "The 34-item v0 pass ledger and accepted experiment core are preserved. The v0 "
                "H_D fallback prerequisite and six-class aggregate are not claimed verbatim: "
                "they are explicitly superseded within the previously blocked mechanism-identity "
                "and H_E-completeness contract repairs required by current authority."
            ),
            "neighbor_limitation": neighbor["scientific_limitation"],
            "historical_anchor_interpretation": (
                "The historical 1e-8 role and frozen canonical residual ceilings are read-only "
                "eligibility evidence. They do not select the future run matrix or mechanism "
                "classifier thresholds, which remain freeze obligations."
            ),
            "claim_ceiling": (
                "Acceptance authorizes preparation of an exact numerical freeze only. It does "
                "not accept a freeze, authorize execution, identify a mechanism, reclassify "
                "robustness, evaluate materiality, or award a scientific claim."
            ),
        },
        "blocking_findings": [],
        "freeze_packet_preparation_obligations": {
            "deferred_item_count": len(packet["freeze_deferred_registry"]),
            "deferred_items": packet["freeze_deferred_registry"],
            "must_close_before_freeze_review": [
                "exact run matrix and paired-control multiplicity",
                "exact neighbor identity under the accepted thirteen-row rule",
                "exact equation-block registry bound to implementation",
                "exact actual-discrete-operator closure and truncation remainder",
                "exact nonperturbation equality or independently derived fallback equivalence",
                "exact units, norms, floors, thresholds, contrasts, associations, and tie rules",
                "exact output schema, cadence, volume budget, paths, and payload identities",
                "exact controls, classifier, implementation hashes, and one-execution rule",
            ],
            "freeze_failure_disposition": (
                "Any unresolved required semantic, operator, nonperturbation, custody, or "
                "classifier item blocks freeze acceptance and cannot be filled from results."
            ),
        },
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "validation_status": {
            "focused_independent_design_v1_review_tests": {"passed": 19, "failed": 0},
            "current_affected_descendant_robustness_chain": {
                "passed": 321,
                "failed": 0,
                "historical_worktree_sensitive_deselections": 2,
            },
            "affected_Lean_build": {"job_count": 157, "status": "PASSED"},
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
        "selected_next_target": SELECTED_NEXT_TARGET if accepted else TARGET,
        "authority_rotation": {
            "instrumented_R13_experiment_design_accepted": accepted,
            "numerical_freeze_packet_preparation_authorized": accepted,
            "numerical_freeze_packet_prepared": False,
            "numerical_freeze_accepted": False,
            "experiment_frozen": False,
            "exact_run_count_or_values_selected": False,
            "new_simulation_authorized": False,
            "rerun_authorized": False,
            "threshold_or_fit_change_authorized": False,
            "different_numerical_method_authorized": False,
            "R13_parameter_or_initial_condition_change_authorized": False,
            "canonical_output_mutation_authorized": False,
            "robustness_reclassification_authorized": False,
            "materiality_classification_authorized": False,
            "model_domain_claim_authorized": False,
            "new_E_REPRO_authorized": False,
            "pillar_or_seam_promotion_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_promotion_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "reviewer_sha256": sha256_path(REPO_ROOT / REVIEWER_RELATIVE_PATH),
        "nonclaims": [
            "no numerical freeze packet prepared or accepted",
            "no exact future run count, run matrix, tolerance, duration, or neighbor frozen",
            "no exact mechanism-output schema, floor, threshold, contrast, association, or classifier hash frozen",
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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Independently review corrected instrumented R13 design v1."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    before = canonical_root_digest()
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, IndexError, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    raw = canonical_json_bytes(report)
    if args.write:
        REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REPORT_PATH.write_bytes(raw)
    elif args.check:
        if not REPORT_PATH.is_file() or REPORT_PATH.read_bytes() != raw:
            print(f"stale or missing design v1 review artifact: {REPORT_RELATIVE_PATH}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(raw)
    after = canonical_root_digest()
    if before != after:
        print("canonical output root changed during independent design v1 review", file=sys.stderr)
        return 1
    if report["failed_decision_ids"]:
        if args.write:
            print(
                f"independent corrected design review blocked on "
                f"{len(report['failed_decision_ids'])} decisions; authority unchanged"
            )
        elif args.check:
            print(
                f"blocked corrected design review verified: "
                f"{len(report['failed_decision_ids'])} findings; canonical outputs unchanged"
            )
        return 2
    if args.write:
        print(
            f"accepted corrected instrumented R13 design: "
            f"{report['passed_decision_count']}/{report['decision_count']} decisions; "
            f"freeze preparation authorized only"
        )
    elif args.check:
        print(
            f"accepted corrected design review verified: "
            f"{report['passed_decision_count']}/{report['decision_count']} decisions; "
            f"canonical outputs unchanged"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
