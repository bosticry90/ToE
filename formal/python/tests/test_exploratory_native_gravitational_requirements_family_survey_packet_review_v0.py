from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_packet_review_v0 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_packet_input_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_PACKET_HASHES
    }
    review.build_review()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_PACKET_HASHES
    }
    assert before == after == review.AUTHORITY_AND_PACKET_HASHES


def test_review_accepts_exactly_one_bounded_manual_survey() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND
    execution = report["authorized_execution"]
    assert execution["execution_count"] == 1
    assert execution["mode"] == (
        "NONAUTHORITATIVE_MANUALLY_ADJUDICATED_EXPLORATION_ONLY"
    )
    assert execution["independent_result_review_required"] is True


def test_all_eight_independent_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 8
    assert gates["failure_count"] == 0
    assert [row["gate"] for row in gates["rows"]] == list(range(1, 9))
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_no_alternate_selector_or_v2_evaluator_path_exists() -> None:
    audit = _report()["no_alternate_selector_audit"]
    assert audit["status"] == "PASS"
    assert audit["forbidden_form_fields_present"] == []
    assert audit["evaluate_analysis_call_present"] is False
    assert audit["v2_evaluator_module_import_present"] is False
    assert set(audit["observed_import_roots"]).issubset({
        "__future__", "argparse", "hashlib", "json", "pathlib", "typing"
    })
    assert not any(
        token in name.lower()
        for name in audit["defined_functions"]
        for token in ("survivor", "classifier", "recommend_theory")
    )


def test_not_surveyed_unresolved_and_incomplete_are_disjoint() -> None:
    audit = _report()["state_and_completeness_audit"]
    assert audit["status"] == "PASS"
    assert audit["canonical_blank_form_count"] == 70
    assert audit["canonical_UNRESOLVED_count"] == 0
    assert audit["observed"] == {
        "canonical_not_surveyed": ["VALID_NOT_SURVEYED"],
        "incomplete_nonblank": "INCOMPLETE_SURVEY_ENTRY",
        "partial_blank": "INCOMPLETE_SURVEY_ENTRY",
        "valid_unresolved": "VALID_PROVISIONAL_ENTRY",
    }


def test_structural_rubric_rejects_each_missing_reasoning_component() -> None:
    prepared = review._load_packet()
    blank = prepared["survey_form_contract"]["forms"][0]
    valid = review._valid_unresolved_fixture(blank)
    assert review.structural_entry_disposition(valid) == "VALID_PROVISIONAL_ENTRY"
    mutations = {
        "concise_rationale": None,
        "assumptions_and_domain": [],
        "source_or_derivation_pointers": [],
        "main_uncertainty": None,
        "resolving_calculation_or_theorem": None,
        "priority_role": "UNASSIGNED",
        "manual_adjudicator_id": None,
        "manual_review_status": "NOT_REVIEWED",
    }
    for field, replacement in mutations.items():
        value = copy.deepcopy(valid)
        value[field] = replacement
        assert review.structural_entry_disposition(value) == (
            "INCOMPLETE_SURVEY_ENTRY"
        ), field


def test_source_scope_and_reasoning_basis_are_separate_from_confidence() -> None:
    audit = _report()["source_scope_and_reasoning_basis_audit"]
    assert audit["status"] == "PASS"
    assert audit["reasoning_basis_types"] == list(review.REASONING_BASIS_TYPES)
    assert audit["special_case_generalization_prohibited"] is True
    assert audit["recovery_limit_generalization_prohibited"] is True
    assert audit["source_custody_confers_relevance"] is False
    assert audit["confidence_upgrades_basis_authority"] is False
    assert audit["basis_authority_selects_confidence_label"] is False


def test_all_eight_questions_are_unanswered_valid_and_direction_changing() -> None:
    audit = _report()["decision_critical_question_audit"]
    assert audit["status"] == "PASS"
    assert audit["question_count"] == 8
    assert audit["answered_question_count"] == 0
    assert audit["all_seventy_cells_required"] is False
    assert audit["decision_critical_questions_first"] is True
    assert all(row["capabilities"] for row in audit["rows"])
    assert all(row["references_only_frozen_requirements"] for row in audit["rows"])
    assert all(row["references_only_frozen_families"] for row in audit["rows"])


def test_family_envelope_is_comparison_only_and_not_exhaustive() -> None:
    audit = _report()["family_envelope_audit"]
    assert audit["status"] == "PASS"
    assert audit["family_count"] == 7
    assert audit["all_family_rows_comparison_only"] is True
    assert audit["presented_as_exhaustive"] is False
    assert audit["expansion_authorized"] is False
    assert audit["material_omission_may_be_recorded_for_future_target"] is True


def test_v2_firewall_remains_closed() -> None:
    audit = _report()["V2_firewall_audit"]
    assert audit["status"] == "PASS"
    assert audit["survey_labels_are_V2_statuses"] is False
    assert audit["survey_results_may_populate_V2_matrix"] is False
    assert audit["v2_evaluator_called"] is False
    assert audit["V2_repair_or_V3_authorized"] is False


def test_three_phase_execution_stops_at_opportunity_map() -> None:
    execution = _report()["authorized_execution"]
    assert execution["phase_1"] == "ANSWER_EIGHT_DECISION_CRITICAL_QUESTIONS"
    assert execution["phase_2"] == "POPULATE_ONLY_SUPPORTING_CELLS"
    assert execution["phase_3"] == (
        "PRODUCE_SCIENTIFIC_OPPORTUNITY_MAP_AND_STOP"
    )
    assert execution["all_seventy_cells_required"] is False
    assert execution["one_next_scientific_investigation_may_be_recommended"] is True


def test_authorization_does_not_promote_or_execute_scientific_result() -> None:
    report = _report()
    boundary = report["authorization_boundary"]
    for key in (
        "manual_provisional_judgments_authorized",
        "literature_supported_comparisons_authorized",
        "transparent_mathematical_reasoning_authorized",
        "unresolved_and_not_surveyed_entries_authorized",
        "next_scientific_investigation_recommendation_authorized",
    ):
        assert boundary[key] is True, key
    for key, value in boundary.items():
        if key not in {
            "manual_provisional_judgments_authorized",
            "literature_supported_comparisons_authorized",
            "transparent_mathematical_reasoning_authorized",
            "unresolved_and_not_surveyed_entries_authorized",
            "next_scientific_investigation_recommendation_authorized",
        }:
            assert value is False, key
    scope = report["scope"]
    assert scope["independent_packet_review_executed"] is True
    assert scope["packet_accepted"] is True
    assert scope["manual_exploratory_survey_executed"] is False
    assert scope["blank_survey_forms_retained"] == 70
    assert scope["provisional_survey_classifications_made"] == 0
    assert scope["decision_critical_questions_answered"] == 0
    assert scope["real_matrix_cells_computed"] == 0


def test_human_review_records_acceptance_rubric_phases_and_nonclaims() -> None:
    text = (REPO_ROOT / review.REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "INCOMPLETE_SURVEY_ENTRY",
        "SURVEYED_PROVISIONAL",
        "NOT_SURVEYED",
        "UNRESOLVED",
        "ESTABLISHED_LITERATURE",
        "EXPERT_JUDGMENT",
        "Phase 1: decision-critical questions",
        "Phase 2: supporting cells only",
        "Phase 3: scientific opportunity map",
        "0 / 70",
        "does not authorize",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
