from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_"
    "20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_"
    "20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_quadratic_gravity_comparison_conditional_mode_selection_envelope_v0.py"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_"
    "20260718_v0.json"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_REVIEW_"
    "20260718_v0.json"
)
TARGET = "execute_post_quadratic_gravity_comparison_conditional_mode_selection_envelope_v0"
VERDICT = "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE"
SELECTED_NEXT_TARGET = (
    "review_post_quadratic_gravity_comparison_conditional_mode_selection_"
    "envelope_v0_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_CONDITIONAL_ENVELOPE_RESULT_REVIEW_ONLY"

REVIEW_HASHES = {
    "formal/docs/lanes/POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_REVIEW_20260718_v0.md":
        "296344da12a0d51b14351b93dc8f0e0874ffc6565325d3eecdf2c3acf3b23483",
    "formal/docs/release/POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_REVIEW_20260718_v0.json":
        "b767f872f2febf3026af9483032a8f3ec30a9b3ebe978c9c1bbd73bb41060348",
    "formal/python/tools/post_quadratic_gravity_comparison_conditional_mode_selection_packet_review_v0.py":
        "b091a6601f2e7b7ea718fe2d5e9de322c0c14ce674e8e95d8584588b1b5130fb",
    "formal/python/tests/test_post_quadratic_gravity_comparison_conditional_mode_selection_packet_review_v0.py":
        "ef6cc1f10f453e263ebca3f7fbfc7248445ce658e335434dca9c1ff88689b341",
    "formal/toe_formal/ToeFormal/Derivation/PostQuadraticGravityComparisonConditionalModeSelectionPacketReviewV0.lean":
        "49669a1823f39e712ed6d053511311a3a1022732461602c5f6cdbdab10b95d20",
}

SUBORDINATE_FINDINGS = (
    "NO_CURRENT_NATIVE_CONDITION_SELECTS_A_BRANCH",
    "STANDARD_CONSISTENCY_CRITERIA_FAVOR_SCALAR_ONLY_OR_EH_BRANCHES",
    "MINIMAL_MODE_CONDITION_WOULD_COLLAPSE_FAMILY_TO_EH",
    "EMPIRICAL_CURRENT_CHANNEL_BOUNDS_BUT_DOES_NOT_EXACTLY_SELECT_BETA",
    "OUTSIDE_FAMILY_MECHANISM_REQUIRES_FRESH_TARGET",
)

CONSEQUENCE_KINDS = {
    "SEL_NATIVE_R9_CURRENT_REPRESENTABILITY": "NO_PARAMETER_SELECTION_EVALUATION_ONLY",
    "SEL_NATIVE_R10_STABILITY_EVALUATION": "NO_PARAMETER_SELECTION_THRESHOLD_ABSENT",
    "SEL_NO_TACHYONIC_POLES": "EXACT_CONDITIONAL_RESTRICTION_NOT_ADOPTED",
    "SEL_NO_NEGATIVE_RESIDUE_SPIN2": "EXACT_CONDITIONAL_POLE_REMOVAL_NOT_ADOPTED",
    "SEL_NO_EXTRA_SCALAR": "EXACT_CONDITIONAL_POLE_REMOVAL_NOT_ADOPTED",
    "SEL_MINIMAL_SPECTRUM": "EXACT_CONDITIONAL_FAMILY_REDUCTION_NOT_ADOPTED",
    "SEL_EXACT_EINSTEIN_0I": "EXACT_COMPARATOR_CONSEQUENCE_NOT_ADOPTED",
    "SEL_FINITE_PRECISION_0I": "EMPIRICAL_BOUND_NOT_EXACT_IDENTITY",
    "SEL_LONG_RANGE_EINSTEIN": "ASYMPTOTIC_OR_DECOUPLING_COMPATIBILITY",
    "SEL_HYPOTHETICAL_MINIMAL_MODE_POSTULATE": "HYPOTHETICAL_CONSEQUENCE_NO_POSTULATE_CREATED",
}

AUTHORITY_EFFECTS = {
    "PROJECT_BOUND_NATIVE_PRINCIPLE": "PROJECT_AUTHORITY_SUPPORTS_EVALUATION_ONLY",
    "SUPPLIED_STANDARD_PHYSICS_CRITERION": "SUPPLIED_CONDITIONAL_CRITERION_NONNATIVE",
    "EMPIRICAL_CONSTRAINT": "FUTURE_EMPIRICAL_BOUND_REQUIRES_DATA",
    "PROPOSED_NEW_POSTULATE": "HYPOTHETICAL_REQUIRES_FRESH_AUTHORITY",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in REVIEW_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"conditional-envelope review authority drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})

    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != (
        "ACCEPTED_AUTHORIZE_ONE_BOUNDED_CONDITIONAL_MODE_SELECTION_ENVELOPE_EXECUTION"
    ):
        raise ValueError("packet review did not accept the bounded execution")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("packet review did not authorize this target")
    boundary = review["authorization_boundary"]
    if boundary.get("one_bounded_envelope_execution_authorized") is not True:
        raise ValueError("single envelope execution not authorized")
    if boundary.get("additional_execution_authorized") is not False:
        raise ValueError("review unexpectedly authorizes additional execution")
    if review["scope"].get("envelope_execution_executed") is not False:
        raise ValueError("authorized execution was already consumed")

    packet = _load_json(PACKET_RELATIVE_PATH)
    packet_hashes = {
        row["relative_path"]: row["sha256"]
        for row in review["authority"]["frozen_packet_artifacts"]
    }
    for relative_path, expected in packet_hashes.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"frozen conditional packet drift: {relative_path}")
    if packet["selector_register"].get("adjudicated_count") != 0:
        raise ValueError("packet did not begin with zero adjudications")
    if packet["selector_register"].get("adopted_count") != 0:
        raise ValueError("packet unexpectedly adopted a condition")
    if packet["outcome_contract"].get("principal_outcome_now") is not None:
        raise ValueError("packet preissued a principal outcome")
    return custody, review, packet


def adjudicate_selector(row: dict[str, Any]) -> dict[str, Any]:
    selector_id = row.get("selector_id")
    if selector_id not in CONSEQUENCE_KINDS:
        raise ValueError(f"unknown selector: {selector_id}")
    authority_class = row.get("authority_class")
    if authority_class not in AUTHORITY_EFFECTS:
        raise ValueError(f"unknown authority class for {selector_id}")
    if row.get("condition_adopted") is not False:
        raise ValueError(f"pre-adopted condition: {selector_id}")
    if row.get("native_selection_weight_now") is not False:
        raise ValueError(f"preloaded native weight: {selector_id}")
    required = (
        "condition",
        "authority_binding",
        "parameter_restriction",
        "remaining_spectrum",
        "remaining_obligations",
    )
    if any(not row.get(field) for field in required):
        raise ValueError(f"incomplete selector record: {selector_id}")
    return {
        "selector_id": selector_id,
        "selector_condition": row["condition"],
        "canonical_provenance": {
            "authority_class": authority_class,
            "authority_binding": row["authority_binding"],
            "authority_effect": AUTHORITY_EFFECTS[authority_class],
        },
        "conditional_parameter_consequence": row["parameter_restriction"],
        "consequence_kind": CONSEQUENCE_KINDS[selector_id],
        "remaining_mode_content": row["remaining_spectrum"],
        "scope": "FROZEN_QUADRATIC_COMPARISON_SCOPE",
        "unresolved_scientific_obligation": list(row["remaining_obligations"]),
        "adjudication_status": "AUTHORITY_CLASSIFIED_CONSEQUENCE_RECORDED_NOT_ADOPTED",
        "native_branch_selection_authority": False,
        "adoption_status": "NOT_ADOPTED",
        "condition_adopted": False,
    }


def classify_principal(
    rows: list[dict[str, Any]], *, authority_complete: bool, logic_scope_valid: bool
) -> str:
    if not authority_complete:
        return "CONDITIONAL_MODE_SELECTION_ENVELOPE_BLOCKED_AUTHORITY"
    if not logic_scope_valid:
        return "CONDITIONAL_MODE_SELECTION_ENVELOPE_BLOCKED_LOGIC_OR_SCOPE"
    if len(rows) != 10 or any(
        row.get("adjudication_status")
        != "AUTHORITY_CLASSIFIED_CONSEQUENCE_RECORDED_NOT_ADOPTED"
        for row in rows
    ):
        return "CONDITIONAL_MODE_SELECTION_ENVELOPE_BLOCKED_AUTHORITY"
    if any(row.get("condition_adopted") for row in rows):
        return "CONDITIONAL_MODE_SELECTION_ENVELOPE_BLOCKED_LOGIC_OR_SCOPE"
    return "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE"


def _execution_controls(value: dict[str, Any]) -> dict[str, Any]:
    rows = value["selector_adjudication"]["rows"]
    by_id = {row["selector_id"]: row for row in rows}
    scope = value["scope"]
    positions = value["position_map"]["rows"]
    checks = [
        ("EXEC_REVIEW_CUSTODY_EXACT", len(value["authority"]["frozen_review_artifacts"]) == 5),
        ("EXEC_EXACT_AUTHORIZED_TARGET", value["target"] == TARGET),
        ("EXEC_SINGLE_AUTHORIZED_RUN_CONSUMED", scope["authorized_execution_consumed"] == 1),
        ("EXEC_TEN_CANONICAL_SELECTORS", len(rows) == 10),
        ("EXEC_SHARED_ADJUDICATION_PATH", all(row["scope"] == "FROZEN_QUADRATIC_COMPARISON_SCOPE" for row in rows)),
        ("EXEC_ALL_SELECTORS_ADJUDICATED", value["selector_adjudication"]["adjudicated_count"] == 10),
        ("EXEC_ZERO_CONDITIONS_ADOPTED", value["selector_adjudication"]["adopted_count"] == 0),
        ("EXEC_R9_REMAINS_EVALUATION_ONLY", by_id["SEL_NATIVE_R9_CURRENT_REPRESENTABILITY"]["conditional_parameter_consequence"] == "NONE_BY_ITSELF"),
        ("EXEC_R10_REMAINS_THRESHOLD_FREE", by_id["SEL_NATIVE_R10_STABILITY_EVALUATION"]["conditional_parameter_consequence"] == "NONE_WITHOUT_AN_ACCEPTANCE_THRESHOLD"),
        ("EXEC_S3_REMAINS_SUPPLIED", by_id["SEL_MINIMAL_SPECTRUM"]["canonical_provenance"]["authority_class"] == "SUPPLIED_STANDARD_PHYSICS_CRITERION"),
        ("EXEC_TACHYON_NOT_HEALTH", "NEGATIVE_RESIDUE" in by_id["SEL_NO_TACHYONIC_POLES"]["remaining_mode_content"]),
        ("EXEC_GHOST_AVOIDANCE_CONDITIONAL_ONLY", by_id["SEL_NO_NEGATIVE_RESIDUE_SPIN2"]["conditional_parameter_consequence"] == "beta=0" and not by_id["SEL_NO_NEGATIVE_RESIDUE_SPIN2"]["condition_adopted"]),
        ("EXEC_EXACT_EMPIRICAL_CURRENT_DISJOINT", by_id["SEL_EXACT_EINSTEIN_0I"]["conditional_parameter_consequence"] == "beta=0" and "not logically inferred" in by_id["SEL_FINITE_PRECISION_0I"]["conditional_parameter_consequence"]),
        ("EXEC_COINCIDENT_MASS_NO_ESCAPE", value["coincident_mass_status"]["ghost_repaired"] is False),
        ("EXEC_THREE_POSITIONS_REMAIN_OPEN", len(positions) == 3 and all(not row["selected"] for row in positions)),
        ("EXEC_EXACTLY_ONE_PRINCIPAL_OUTCOME", value["principal_classification"]["outcome_count"] == 1 and value["verdict"] == VERDICT),
        ("EXEC_FIVE_SUBORDINATE_FINDINGS_NONADOPTIVE", tuple(value["subordinate_findings"]) == SUBORDINATE_FINDINGS),
        ("EXEC_STOP_FOR_INDEPENDENT_RESULT_REVIEW", value["selected_next_target"] == SELECTED_NEXT_TARGET and scope["independent_result_review_required"] is True),
    ]
    return {
        "control_count": len(checks),
        "pass_count": sum(passed for _, passed in checks),
        "failure_count": sum(not passed for _, passed in checks),
        "rows": [
            {"control_id": control_id, "status": "PASSED" if passed else "FAILED", "uses_shared_execution_path": True}
            for control_id, passed in checks
        ],
    }


def build_execution() -> dict[str, Any]:
    custody, review, packet = _validate_authority()
    human = REPO_ROOT / HUMAN_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("conditional-envelope human record or test missing")
    adjudicated = [adjudicate_selector(row) for row in packet["selector_register"]["rows"]]
    principal = classify_principal(
        adjudicated, authority_complete=True, logic_scope_valid=True
    )
    if principal != VERDICT:
        raise ValueError(f"unexpected principal classification: {principal}")

    value: dict[str, Any] = {
        "schema_id": "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": principal,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "authorized_execution_count": 1,
            "consumed_execution_count": 1,
            "consumed_packet_review_verdict": review["verdict"],
            "frozen_review_artifacts": custody,
            "human_execution": {"relative_path": HUMAN_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "accepted_conditional_physics": packet["accepted_comparison_input"],
        "selector_adjudication": {
            "selector_count": len(adjudicated),
            "adjudicated_count": len(adjudicated),
            "adopted_count": sum(row["condition_adopted"] for row in adjudicated),
            "shared_path": "resolve provenance -> reproduce consequence -> classify meaning -> record spectrum and obligation -> prohibit adoption",
            "rows": adjudicated,
        },
        "principal_classification": {
            "outcome": principal,
            "outcome_count": 1,
            "native_selector_count": 0,
            "meaning": "All ten authority records are classified, and no current project-native condition selects a branch.",
        },
        "subordinate_findings": list(SUBORDINATE_FINDINGS),
        "position_map": {
            "position_count": 3,
            "selected_count": 0,
            "rows": [
                {"position": "A_EXCLUDE_NEGATIVE_RESIDUE_SPIN2_ONLY", "status": "OPEN_NOT_SELECTED", "selected": False, "authority_needed": "adopt supplied ghost-avoidance criterion or derive a native equivalent"},
                {"position": "B_REQUIRE_MINIMAL_MODE_CONTENT", "status": "OPEN_NOT_SELECTED", "selected": False, "authority_needed": "native justification for minimal gravitational spectrum"},
                {"position": "C_CHANGE_THEORY_CLASS", "status": "OPEN_NOT_SELECTED_FRESH_TARGET_REQUIRED", "selected": False, "authority_needed": "fresh scientific target and mechanism-specific derivation"},
            ],
        },
        "exact_empirical_current_classification": {
            "exact_theoretical_equality": "beta=0 within frozen family",
            "finite_precision_observation": "parameter bound dependent on range source and uncertainty",
            "exact_beta_zero_from_finite_data_licensed": False,
            "dataset_imported": False,
            "metric_to_observable_transport_executed": False,
        },
        "coincident_mass_status": {
            "condition": "2 alpha+beta=0 with beta!=0",
            "pole_locations_coincide": True,
            "P2_P0s_orthogonal": True,
            "double_pole": False,
            "mode_merger": False,
            "cancellation": False,
            "ghost_repaired": False,
        },
        "scope_firewall": packet["scope_firewall"],
        "claim_ceiling": "Authority-aware conditional classification only. No condition, branch, native principle, postulate, coupling, gravitational action, outside-family mechanism, dataset, empirical fit, matter sector, new metric variation, orbital transport, frame-dragging result, GR-pillar promotion, V2 cell, or master-action change is selected or authorized.",
        "scope": {
            "authorized_execution_consumed": 1,
            "envelope_execution_completed": True,
            "selector_adjudication_completed": True,
            "principal_classification_issued": True,
            "independent_result_review_required": True,
            "condition_adopted": False,
            "branch_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_proposed_or_authorized": False,
            "alpha_or_beta_selected": False,
            "gravitational_action_selected": False,
            "outside_family_mechanism_opened": False,
            "dataset_or_empirical_fit_imported": False,
            "matter_sector_selected": False,
            "new_metric_variation_executed": False,
            "orbital_transport_executed": False,
            "frame_dragging_reopened": False,
            "GR_pillar_promoted": False,
            "authoritative_V2_matrix_populated": False,
            "master_action_mutated": False,
            "additional_execution_authorized": False,
        },
        "current_posture": {
            "conditional_envelope_execution": "COMPLETED_ONCE",
            "result_status": "PENDING_INDEPENDENT_REVIEW",
            "selector_adjudications": "10_OF_10",
            "conditions_adopted": 0,
            "native_branch_selectors": 0,
            "open_positions": "3_OF_3",
            "authoritative_V2_matrix": "0_OF_70",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "frame_dragging": "NOT_RESUMED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
    }
    value["execution_controls"] = _execution_controls(value)
    if value["execution_controls"]["failure_count"]:
        raise ValueError("conditional-envelope execution control failure")
    return value


def artifact_bytes() -> bytes:
    return (json.dumps(build_execution(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Execute the bounded conditional mode-selection envelope.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("conditional_mode_selection_envelope_v0: wrote complete authority classification")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("conditional_mode_selection_envelope_v0: FAILED artifact drift")
        return 1
    print("conditional_mode_selection_envelope_v0: OK selectors=10/10 adopted=0 principal=1 controls=18/18")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
