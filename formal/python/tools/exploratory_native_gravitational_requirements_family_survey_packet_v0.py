from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]

REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_PACKET_"
    "20260718_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_exploratory_native_gravitational_requirements_family_survey_packet_v0.py"
)
HUMAN_PACKET_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_PACKET_"
    "20260718_v0.md"
)
V2_PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "20260718_v2.json"
)
V2_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "REVIEW_20260718_v2.json"
)

TARGET = "prepare_exploratory_native_gravitational_requirements_family_survey_v0"
VERDICT = "PREPARED_PENDING_INDEPENDENT_REVIEW"
SELECTED_NEXT_TARGET = (
    "review_exploratory_native_gravitational_requirements_family_survey_"
    "packet_v0_result"
)
MODE = "NONAUTHORITATIVE_MANUALLY_ADJUDICATED_EXPLORATION"

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/lanes/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_REVIEW_20260718_v2.md":
        "f72b793eadd4db520e30d3af5d0f22a5735d3451639ea092740a97eae3cb5b31",
    V2_REVIEW_RELATIVE_PATH:
        "1faacbd470ef5feed6aebb4dfad34e2e5a9214fa2e31a79d57c375a08f4d9051",
    "formal/python/tools/native_gravitational_principle_requirements_and_action_selection_packet_review_v2.py":
        "28638172711ecb90528db51682a80f0fe5bee388d7c2b9e385e6590b0985b2f6",
    "formal/python/tests/test_native_gravitational_principle_requirements_and_action_selection_packet_review_v2.py":
        "2ee4d32f6f96b7a90720bb5efa2fb2c0e86fd935744aad189ab3b1adbd6e2ea5",
    "formal/toe_formal/ToeFormal/Derivation/NativeGravitationalPrincipleRequirementsAndActionSelectionPacketReviewV2.lean":
        "52b1147a6d5c5cd5a1f3d470df04aa7d1d7eaafb474366ca961cb80479adba22",
    HUMAN_PACKET_RELATIVE_PATH:
        "47956a32c8f833277c6a7d004900e7af63a2e3674a3585aca0351311047c52a5",
}

EXPECTED_REQUIREMENT_IDS = (
    "R1_DIMENSION",
    "R2_METRIC_ONLY",
    "R3_LOCALITY",
    "R4_DIFF_COVARIANCE",
    "R5_CK_FIREWALL",
    "R6_LOCAL_VARIATION",
    "R7_SOURCE_COMPATIBILITY",
    "R8_NEWTON_POISSON",
    "R9_MOMENTUM_CURRENT",
    "R10_STABILITY_NO_FIT",
)

EXPECTED_FAMILY_IDS = (
    "F_EH",
    "F_FR",
    "F_QUADRATIC",
    "F_EXTRA_FIELD",
    "F_NONLOCAL",
    "F_CONNECTION_TORSION",
    "F_EQUIVALENCE_PROBE",
)

PERMITTED_PROVISIONAL_LABELS = (
    "CLEARLY COMPATIBLE",
    "LIKELY COMPATIBLE",
    "LIKELY INCOMPATIBLE",
    "CLEARLY INCOMPATIBLE",
    "UNRESOLVED",
    "OUTSIDE FROZEN SCOPE",
)

WORKFLOW_SENTINEL = "NOT_SURVEYED"
PRIORITY_ROLES = (
    "DECISION_CRITICAL",
    "CONTEXTUAL",
    "DEFERRED",
    "UNASSIGNED",
)

CELL_FIELD_ORDER = (
    "cell_id",
    "requirement_id",
    "family_id",
    "workflow_state",
    "provisional_classification",
    "concise_rationale",
    "assumptions_and_domain",
    "source_or_derivation_pointers",
    "main_uncertainty",
    "resolving_calculation_or_theorem",
    "priority_role",
    "manual_adjudicator_id",
    "manual_review_status",
)

DECISION_CRITICAL_QUESTIONS = (
    {
        "question_id": "DQ1_DIFF_COVARIANCE_DISCRIMINATION",
        "question": (
            "Does R4_DIFF_COVARIANCE discriminate among F_EH, F_FR, and "
            "F_QUADRATIC, or impose only a symmetry common to them?"
        ),
        "requirement_ids": ["R4_DIFF_COVARIANCE"],
        "family_ids": ["F_EH", "F_FR", "F_QUADRATIC"],
    },
    {
        "question_id": "DQ2_CK_FIREWALL_ACTION_RELEVANCE",
        "question": (
            "Does R5_CK_FIREWALL constrain gravitational action form or only "
            "the project architecture surrounding an action?"
        ),
        "requirement_ids": ["R5_CK_FIREWALL"],
        "family_ids": ["F_EH", "F_FR", "F_QUADRATIC"],
    },
    {
        "question_id": "DQ3_SOURCE_COMPATIBILITY_DISCRIMINATION",
        "question": (
            "Does R7_SOURCE_COMPATIBILITY distinguish primary metric families "
            "after coupling, conservation, and field-equation order are explicit?"
        ),
        "requirement_ids": ["R7_SOURCE_COMPATIBILITY"],
        "family_ids": ["F_EH", "F_FR", "F_QUADRATIC"],
    },
    {
        "question_id": "DQ4_NEWTONIAN_RECOVERY_DISCRIMINATION",
        "question": (
            "Can R8_NEWTON_POISSON distinguish nonlinear or quadratic curvature "
            "families from F_EH without tuning a special parameter limit?"
        ),
        "requirement_ids": ["R8_NEWTON_POISSON"],
        "family_ids": ["F_EH", "F_FR", "F_QUADRATIC"],
    },
    {
        "question_id": "DQ5_MOMENTUM_CURRENT_INDEPENDENCE",
        "question": (
            "Does R9_MOMENTUM_CURRENT add a discriminator independent of R8, "
            "and which linearized derivations would establish that?"
        ),
        "requirement_ids": ["R8_NEWTON_POISSON", "R9_MOMENTUM_CURRENT"],
        "family_ids": ["F_EH", "F_FR", "F_QUADRATIC"],
    },
    {
        "question_id": "DQ6_STABILITY_NO_FIT_DISCRIMINATION",
        "question": (
            "What R10_STABILITY_NO_FIT calculation would materially distinguish "
            "F_FR and F_QUADRATIC from F_EH?"
        ),
        "requirement_ids": ["R10_STABILITY_NO_FIT"],
        "family_ids": ["F_EH", "F_FR", "F_QUADRATIC"],
    },
    {
        "question_id": "DQ7_NATIVE_SEAM_LAGRANGIAN_CONSTRAINT",
        "question": (
            "Does any accepted ToE-specific seam or admissibility principle "
            "constrain the gravitational Lagrangian rather than its evaluation?"
        ),
        "requirement_ids": ["R5_CK_FIREWALL", "R7_SOURCE_COMPATIBILITY"],
        "family_ids": ["F_EH", "F_FR", "F_QUADRATIC"],
    },
    {
        "question_id": "DQ8_PROPERTY_SCOPED_EQUIVALENCE",
        "question": (
            "For F_EQUIVALENCE_PROBE, which exact properties survive each "
            "boundary, algebraic, or topological equivalence?"
        ),
        "requirement_ids": list(EXPECTED_REQUIREMENT_IDS),
        "family_ids": ["F_EQUIVALENCE_PROBE"],
    },
)


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _load_object(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    frozen: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"exploratory survey authority hash mismatch: {relative_path}")
        frozen.append({"relative_path": relative_path, "sha256": observed})

    review = _load_object(V2_REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "BLOCKED_CLOSE_AUTOMATED_ACTION_SELECTION_TOOLING_LANE":
        raise ValueError("V2 automated lane closure verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("V2 review did not authorize survey preparation")
    if review["lane_closure"].get("automatic_v3_authorized") is not False:
        raise ValueError("automatic V3 prohibition missing")
    if review["scope"].get("real_matrix_cells_computed") != 0:
        raise ValueError("V2 review real-matrix boundary mismatch")
    if review["exploratory_boundary"].get("nonauthoritative") is not True:
        raise ValueError("V2 review did not authorize nonauthoritative exploration")
    return frozen, review


def _frozen_catalogs() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    v2_packet = _load_object(V2_PACKET_RELATIVE_PATH)
    requirement_contract = v2_packet["authority_derived_requirement_contract"]
    family_contract = v2_packet["family_envelope_contract"]
    requirements = requirement_contract["project_rows"]
    families = family_contract["rows"]
    requirement_ids = tuple(row["requirement_id"] for row in requirements)
    family_ids = tuple(row["family_id"] for row in families)
    if requirement_ids != EXPECTED_REQUIREMENT_IDS:
        raise ValueError("frozen exploratory requirement inventory drift")
    if family_ids != EXPECTED_FAMILY_IDS:
        raise ValueError("frozen exploratory family inventory drift")
    return requirements, families


def _blank_cell(requirement_id: str, family_id: str) -> dict[str, Any]:
    row = {
        "cell_id": f"EXP_{requirement_id}__{family_id}",
        "requirement_id": requirement_id,
        "family_id": family_id,
        "workflow_state": WORKFLOW_SENTINEL,
        "provisional_classification": None,
        "concise_rationale": None,
        "assumptions_and_domain": [],
        "source_or_derivation_pointers": [],
        "main_uncertainty": None,
        "resolving_calculation_or_theorem": None,
        "priority_role": "UNASSIGNED",
        "manual_adjudicator_id": None,
        "manual_review_status": "NOT_REVIEWED",
    }
    if tuple(row) != CELL_FIELD_ORDER:
        raise ValueError("blank survey-cell schema drift")
    return row


def _blank_survey_forms() -> list[dict[str, Any]]:
    return [
        _blank_cell(requirement_id, family_id)
        for requirement_id in EXPECTED_REQUIREMENT_IDS
        for family_id in EXPECTED_FAMILY_IDS
    ]


def _question_rows() -> list[dict[str, Any]]:
    return [
        {
            **question,
            "answered": False,
            "exploratory_answer": None,
            "priority_rank": None,
            "resolving_work_ids": [],
        }
        for question in DECISION_CRITICAL_QUESTIONS
    ]


def _preparation_controls(
    requirements: list[dict[str, Any]],
    families: list[dict[str, Any]],
    forms: list[dict[str, Any]],
    questions: list[dict[str, Any]],
) -> dict[str, Any]:
    rows = [
        {
            "control_id": "CTRL_EXACT_FROZEN_REQUIREMENT_INVENTORY",
            "passed": tuple(row["requirement_id"] for row in requirements)
            == EXPECTED_REQUIREMENT_IDS,
        },
        {
            "control_id": "CTRL_EXACT_FROZEN_FAMILY_INVENTORY",
            "passed": tuple(row["family_id"] for row in families)
            == EXPECTED_FAMILY_IDS,
        },
        {
            "control_id": "CTRL_EXACT_SEVENTY_BLANK_FORMS",
            "passed": len(forms) == 70 and len({row["cell_id"] for row in forms}) == 70,
        },
        {
            "control_id": "CTRL_ZERO_PROVISIONAL_CLASSIFICATIONS",
            "passed": all(row["provisional_classification"] is None for row in forms),
        },
        {
            "control_id": "CTRL_ZERO_SCIENTIFIC_CONTENT_IN_FORMS",
            "passed": all(
                row["workflow_state"] == WORKFLOW_SENTINEL
                and row["concise_rationale"] is None
                and row["assumptions_and_domain"] == []
                and row["source_or_derivation_pointers"] == []
                and row["main_uncertainty"] is None
                and row["resolving_calculation_or_theorem"] is None
                and row["priority_role"] == "UNASSIGNED"
                and row["manual_adjudicator_id"] is None
                and row["manual_review_status"] == "NOT_REVIEWED"
                for row in forms
            ),
        },
        {
            "control_id": "CTRL_EXACT_SIX_PROVISIONAL_LABELS",
            "passed": len(PERMITTED_PROVISIONAL_LABELS) == 6
            and len(set(PERMITTED_PROVISIONAL_LABELS)) == 6,
        },
        {
            "control_id": "CTRL_EIGHT_DECISION_QUESTIONS_UNANSWERED",
            "passed": len(questions) == 8
            and all(
                row["answered"] is False
                and row["exploratory_answer"] is None
                and row["priority_rank"] is None
                and row["resolving_work_ids"] == []
                for row in questions
            ),
        },
        {
            "control_id": "CTRL_NO_V2_MATRIX_OR_TERMINAL_FIELDS",
            "passed": all(
                not {
                    "cell_status",
                    "evidence_id",
                    "claim_scope",
                    "scientific_outcome",
                    "survivor_set",
                    "equivalence_class",
                }.intersection(row)
                for row in forms
            ),
        },
    ]
    return {
        "control_count": len(rows),
        "control_pass_count": sum(row["passed"] for row in rows),
        "rows": rows,
    }


def build_packet() -> dict[str, Any]:
    frozen_inputs, review = _validate_authority()
    requirements, families = _frozen_catalogs()
    forms = _blank_survey_forms()
    questions = _question_rows()
    controls = _preparation_controls(requirements, families, forms, questions)
    if controls["control_count"] != controls["control_pass_count"]:
        raise ValueError("exploratory survey preparation control failure")

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.is_file():
        raise ValueError("exploratory survey packet focused test missing")
    return {
        "schema_id": (
            "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_"
            "PACKET_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "mode": MODE,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "INDEPENDENT_NONAUTHORITATIVE_SURVEY_PREPARATION_REVIEW_ONLY"
        ),
        "authority": {
            "consumed_v2_review_verdict": review["verdict"],
            "automated_action_selection_tooling_lane": "CLOSED",
            "frozen_inputs": frozen_inputs,
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "mode_contract": {
            "exploratory": True,
            "nonauthoritative": True,
            "manually_adjudicated": True,
            "hypothesis_generating": True,
            "automated_scientific_adjudication": False,
            "survey_labels_are_V2_statuses": False,
            "survey_results_may_populate_V2_matrix": False,
            "survivor_reducer_present": False,
            "equivalence_reducer_present": False,
            "terminal_classifier_present": False,
            "automatic_V3_authorized": False,
        },
        "frozen_requirement_catalog": {
            "requirement_count": len(requirements),
            "requirement_ids": list(EXPECTED_REQUIREMENT_IDS),
            "rows": requirements,
        },
        "frozen_family_catalog": {
            "family_count": len(families),
            "family_ids": list(EXPECTED_FAMILY_IDS),
            "rows": families,
            "expanded_for_survey": False,
        },
        "survey_vocabulary": {
            "workflow_sentinel": WORKFLOW_SENTINEL,
            "permitted_provisional_classification_count": len(
                PERMITTED_PROVISIONAL_LABELS
            ),
            "permitted_provisional_classifications": list(
                PERMITTED_PROVISIONAL_LABELS
            ),
            "priority_roles": list(PRIORITY_ROLES),
            "V2_status_aliasing_prohibited": True,
        },
        "survey_form_contract": {
            "cell_field_order": list(CELL_FIELD_ORDER),
            "blank_form_count": len(forms),
            "provisional_classification_count": 0,
            "rationale_count": 0,
            "source_or_derivation_pointer_count": 0,
            "manual_adjudicator_count": 0,
            "forms": forms,
        },
        "source_and_derivation_policy": {
            "permitted_pointer_roles": [
                "PROJECT_AUTHORITY_REQUIREMENT_SOURCE",
                "PRIMARY_MATHEMATICAL_OR_THEORETICAL_SOURCE",
                "DIRECT_DERIVATION",
                "REVIEW_OR_ORIENTATION_SOURCE",
                "SUPPLIED_STANDARD_PHYSICS_COMPARATOR_ONLY",
                "NO_SOURCE_POINTER_IDENTIFIED",
            ],
            "every_surveyed_cell_requires_pointer_or_explicit_absence": True,
            "source_custody_is_scientific_relevance": False,
            "special_case_may_stand_for_whole_family": False,
            "recovery_limit_may_stand_for_whole_family": False,
            "clearly_label_prefers_primary_source_theorem_or_derivation": True,
            "likely_label_requires_named_gap": True,
            "unresolved_label_requires_named_resolving_work": True,
            "self_certification_creates_authoritative_evidence": False,
        },
        "decision_critical_question_register": {
            "question_count": len(questions),
            "answered_question_count": 0,
            "rows": questions,
            "supplied_no_extra_mode_is_native_discriminator": False,
            "supplied_second_order_is_native_discriminator": False,
        },
        "execution_protocol_after_acceptance": {
            "execution_count_authorized_by_future_acceptance": 1,
            "decision_critical_questions_first": True,
            "all_seventy_cells_required_for_success": False,
            "unworked_cells_remain_NOT_SURVEYED": True,
            "manufactured_completeness_prohibited": True,
            "required_outputs": [
                "human-readable table of surveyed entries",
                "explicit NOT_SURVEYED inventory",
                "requirement-dependency and redundancy hypotheses",
                "family-difference map without asserted merges",
                "ranked decision-critical calculations or theorems",
                "literature-dispute and domain-restriction notes",
                "exploratory statement on whether a native discriminator was found",
                "nonclaims and stopping boundary",
            ],
            "stop_for_independent_result_review": True,
        },
        "preparation_controls": controls,
        "acceptance_boundary": {
            "acceptance_authorizes_manual_exploratory_survey_only": True,
            "acceptance_authorizes_authoritative_matrix": False,
            "acceptance_authorizes_survivor_set": False,
            "acceptance_authorizes_scientific_outcome": False,
            "acceptance_authorizes_action_or_postulate": False,
            "acceptance_authorizes_metric_variation": False,
            "acceptance_authorizes_frame_dragging": False,
            "acceptance_authorizes_family_envelope_expansion": False,
            "acceptance_authorizes_V2_repair_or_V3": False,
        },
        "scope": {
            "exploratory_survey_packet_prepared": True,
            "independent_packet_review_executed": False,
            "manual_exploratory_survey_executed": False,
            "blank_survey_forms_prepared": 70,
            "provisional_survey_classifications_made": 0,
            "survey_rationales_authored": 0,
            "decision_critical_questions_answered": 0,
            "real_matrix_cells_computed": 0,
            "real_family_judgment_made": False,
            "real_equivalence_class_established": False,
            "real_survivor_matrix_computed": False,
            "real_scientific_outcome_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "gravitational_action_proposed_or_selected": False,
            "standard_GR_comparator_activated": False,
            "matter_sector_selected": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
            "gravitomagnetic_route_reopened": False,
            "family_envelope_expanded": False,
            "automated_action_selection_tooling_lane_reopened": False,
            "automatic_V3_authorized": False,
            "automation_created": False,
        },
        "current_posture": {
            "minimal_gravitational_sector_contract": "ACCEPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "requirements_action_selection_V2": (
                "BLOCKED_PROJECT_EVIDENCE_SEMANTICS_UNSOUND"
            ),
            "automated_action_selection_tooling": "CLOSED",
            "exploratory_survey_packet_V0": VERDICT,
            "survey_forms": "70_BLANK",
            "provisional_survey_classifications": 0,
            "real_scientific_matrix": "0_OF_70",
            "real_family_judgments": "NONE",
            "automatic_V3": "NOT_AUTHORIZED",
            "gravitational_action": "NOT_SELECTED",
            "metric_variation": "NOT_EXECUTED",
            "frame_dragging": "BLOCKED_UPSTREAM",
        },
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True)
        + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate or check the exploratory gravity survey preparation."
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("exploratory gravity survey packet artifact drift")
        print(json.dumps({
            "status": "VERIFIED",
            "verdict": VERDICT,
            "blank_forms": 70,
            "provisional_classifications": 0,
            "real_matrix_cells": 0,
            "automatic_V3_authorized": False,
        }, sort_keys=True))
        return 0
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
