from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_packet_v0 as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_exactly_and_deterministically() -> None:
    assert packet.artifact_bytes() == packet.artifact_bytes() == REPORT_PATH.read_bytes()


def test_packet_preserves_closed_v2_review_and_human_packet_bytes() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in packet.AUTHORITY_AND_SOURCE_HASHES
    }
    packet.build_packet()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in packet.AUTHORITY_AND_SOURCE_HASHES
    }
    assert before == after == packet.AUTHORITY_AND_SOURCE_HASHES


def test_packet_consumes_only_authorized_exploratory_preparation_target() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["mode"] == packet.MODE
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "INDEPENDENT_NONAUTHORITATIVE_SURVEY_PREPARATION_REVIEW_ONLY"
    )
    assert report["authority"]["consumed_v2_review_verdict"] == (
        "BLOCKED_CLOSE_AUTOMATED_ACTION_SELECTION_TOOLING_LANE"
    )
    assert report["authority"]["automated_action_selection_tooling_lane"] == (
        "CLOSED"
    )


def test_exact_frozen_ten_by_seven_envelope_is_retained() -> None:
    report = _report()
    requirements = report["frozen_requirement_catalog"]
    families = report["frozen_family_catalog"]
    assert requirements["requirement_count"] == 10
    assert requirements["requirement_ids"] == list(packet.EXPECTED_REQUIREMENT_IDS)
    assert [row["requirement_id"] for row in requirements["rows"]] == list(
        packet.EXPECTED_REQUIREMENT_IDS
    )
    assert families["family_count"] == 7
    assert families["family_ids"] == list(packet.EXPECTED_FAMILY_IDS)
    assert [row["family_id"] for row in families["rows"]] == list(
        packet.EXPECTED_FAMILY_IDS
    )
    assert families["expanded_for_survey"] is False


def test_all_seventy_forms_are_blank_and_contain_no_judgment() -> None:
    contract = _report()["survey_form_contract"]
    forms = contract["forms"]
    assert contract["blank_form_count"] == len(forms) == 70
    assert len({row["cell_id"] for row in forms}) == 70
    assert contract["provisional_classification_count"] == 0
    assert contract["rationale_count"] == 0
    assert contract["source_or_derivation_pointer_count"] == 0
    assert contract["manual_adjudicator_count"] == 0
    for row in forms:
        assert set(row) == set(packet.CELL_FIELD_ORDER)
        assert row["workflow_state"] == "NOT_SURVEYED"
        assert row["provisional_classification"] is None
        assert row["concise_rationale"] is None
        assert row["assumptions_and_domain"] == []
        assert row["source_or_derivation_pointers"] == []
        assert row["main_uncertainty"] is None
        assert row["resolving_calculation_or_theorem"] is None
        assert row["priority_role"] == "UNASSIGNED"
        assert row["manual_adjudicator_id"] is None
        assert row["manual_review_status"] == "NOT_REVIEWED"


def test_provisional_vocabulary_is_exact_and_not_a_v2_alias() -> None:
    vocabulary = _report()["survey_vocabulary"]
    assert vocabulary["workflow_sentinel"] == "NOT_SURVEYED"
    assert vocabulary["permitted_provisional_classification_count"] == 6
    assert vocabulary["permitted_provisional_classifications"] == list(
        packet.PERMITTED_PROVISIONAL_LABELS
    )
    assert vocabulary["V2_status_aliasing_prohibited"] is True
    assert set(vocabulary["priority_roles"]) == set(packet.PRIORITY_ROLES)


def test_eight_decision_critical_questions_are_registered_but_unanswered() -> None:
    register = _report()["decision_critical_question_register"]
    rows = register["rows"]
    assert register["question_count"] == len(rows) == 8
    assert register["answered_question_count"] == 0
    assert len({row["question_id"] for row in rows}) == 8
    assert all(row["answered"] is False for row in rows)
    assert all(row["exploratory_answer"] is None for row in rows)
    assert all(row["priority_rank"] is None for row in rows)
    assert all(row["resolving_work_ids"] == [] for row in rows)
    assert register["supplied_no_extra_mode_is_native_discriminator"] is False
    assert register["supplied_second_order_is_native_discriminator"] is False


def test_source_policy_requires_relevance_explanation_not_custody_metadata() -> None:
    policy = _report()["source_and_derivation_policy"]
    assert policy["every_surveyed_cell_requires_pointer_or_explicit_absence"] is True
    assert policy["source_custody_is_scientific_relevance"] is False
    assert policy["special_case_may_stand_for_whole_family"] is False
    assert policy["recovery_limit_may_stand_for_whole_family"] is False
    assert policy["likely_label_requires_named_gap"] is True
    assert policy["unresolved_label_requires_named_resolving_work"] is True
    assert policy["self_certification_creates_authoritative_evidence"] is False


def test_preparation_does_not_import_or_call_closed_v2_evaluator() -> None:
    source = (REPO_ROOT / "formal/python/tools/exploratory_native_gravitational_requirements_family_survey_packet_v0.py").read_text(
        encoding="utf-8"
    )
    assert (
        "import native_gravitational_principle_requirements_and_action_selection_packet_v2"
        not in source
    )
    assert "evaluate_analysis(" not in source
    mode = _report()["mode_contract"]
    assert mode["automated_scientific_adjudication"] is False
    assert mode["survivor_reducer_present"] is False
    assert mode["equivalence_reducer_present"] is False
    assert mode["terminal_classifier_present"] is False


def test_all_preparation_controls_pass_without_scientific_validation_claim() -> None:
    controls = _report()["preparation_controls"]
    assert controls["control_count"] == controls["control_pass_count"] == 8
    assert all(row["passed"] is True for row in controls["rows"])


def test_acceptance_boundary_authorizes_only_one_manual_exploratory_survey() -> None:
    report = _report()
    protocol = report["execution_protocol_after_acceptance"]
    assert protocol["execution_count_authorized_by_future_acceptance"] == 1
    assert protocol["decision_critical_questions_first"] is True
    assert protocol["all_seventy_cells_required_for_success"] is False
    assert protocol["unworked_cells_remain_NOT_SURVEYED"] is True
    assert protocol["manufactured_completeness_prohibited"] is True
    assert protocol["stop_for_independent_result_review"] is True
    boundary = report["acceptance_boundary"]
    assert boundary["acceptance_authorizes_manual_exploratory_survey_only"] is True
    for key, value in boundary.items():
        if key != "acceptance_authorizes_manual_exploratory_survey_only":
            assert value is False, key


def test_real_analysis_and_downstream_physics_remain_unexecuted() -> None:
    scope = _report()["scope"]
    assert scope["exploratory_survey_packet_prepared"] is True
    assert scope["blank_survey_forms_prepared"] == 70
    assert scope["provisional_survey_classifications_made"] == 0
    assert scope["survey_rationales_authored"] == 0
    assert scope["decision_critical_questions_answered"] == 0
    assert scope["real_matrix_cells_computed"] == 0
    for key in (
        "independent_packet_review_executed",
        "manual_exploratory_survey_executed",
        "real_family_judgment_made",
        "real_equivalence_class_established",
        "real_survivor_matrix_computed",
        "real_scientific_outcome_selected",
        "native_gravitational_principle_identified",
        "new_postulate_authorized",
        "gravitational_action_proposed_or_selected",
        "standard_GR_comparator_activated",
        "matter_sector_selected",
        "metric_or_tetrad_variation_executed",
        "stress_energy_derived",
        "tensor_field_equation_derived",
        "gravitomagnetic_route_reopened",
        "family_envelope_expanded",
        "automated_action_selection_tooling_lane_reopened",
        "automatic_V3_authorized",
        "automation_created",
    ):
        assert scope[key] is False, key


def test_human_packet_records_exploratory_boundary_and_zero_judgments() -> None:
    text = (REPO_ROOT / packet.HUMAN_PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        packet.MODE,
        "70 BLANK",
        "0 / 70",
        "NOT_SURVEYED",
        "CLEARLY COMPATIBLE",
        "OUTSIDE FROZEN SCOPE",
        "Decision-critical question register",
        "does not perform the survey",
        "creating V3",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
