from __future__ import annotations

import ast
import json
from pathlib import Path

from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_packet_review_v0 as review,
)
from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_v0 as survey,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / survey.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_survey_regenerates_exactly_and_consumes_accepted_authority() -> None:
    assert survey.artifact_bytes() == survey.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == survey.TARGET
    assert report["verdict"] == survey.VERDICT
    assert report["selected_next_target"] == survey.SELECTED_NEXT_TARGET
    assert report["authority"]["accepted_packet_review_verdict"] == review.VERDICT
    assert report["authority"]["authorized_execution_count"] == 1
    assert report["authority"]["execution_consumed_count"] == 1


def test_all_eight_questions_are_answered_before_cell_summary() -> None:
    register = _report()["decision_critical_question_register"]
    assert register["question_count"] == register["answered_question_count"] == 8
    rows = register["rows"]
    assert {row["priority_rank"] for row in rows} == set(range(1, 9))
    for row in rows:
        assert row["status"] == "ANSWERED_PROVISIONAL"
        assert row["provisional_answer"]
        assert row["assumptions"]
        assert row["reasoning_basis_types"]
        assert row["source_ids"]
        assert row["uncertainty"]
        assert row["resolving_work"]
        assert row["supporting_cell_ids"]
        assert row["authority"] == "EXPLORATORY_NONAUTHORITATIVE"


def test_exactly_22_cells_are_surveyed_and_48_remain_not_surveyed() -> None:
    contract = _report()["survey_form_contract"]
    assert contract["possible_relationship_count"] == 70
    assert contract["surveyed_provisional_count"] == 22
    assert contract["not_surveyed_count"] == 48
    assert contract["incomplete_entry_count"] == 0
    assert len(contract["forms"]) == 70
    assert len(contract["explicit_NOT_SURVEYED_cell_ids"]) == 48
    dispositions = [
        review.structural_entry_disposition(row) for row in contract["forms"]
    ]
    assert dispositions.count("VALID_PROVISIONAL_ENTRY") == 22
    assert dispositions.count("VALID_NOT_SURVEYED") == 48
    assert "INCOMPLETE_SURVEY_ENTRY" not in dispositions


def test_not_surveyed_never_becomes_unresolved() -> None:
    forms = _report()["survey_form_contract"]["forms"]
    blank = [row for row in forms if row["workflow_state"] == "NOT_SURVEYED"]
    unresolved = [
        row for row in forms
        if row["provisional_classification"] == "UNRESOLVED"
    ]
    assert len(blank) == 48
    assert len(unresolved) == 5
    assert all(row["provisional_classification"] is None for row in blank)
    assert all(row["workflow_state"] == "SURVEYED_PROVISIONAL" for row in unresolved)


def test_descriptive_label_tally_is_exact_and_not_a_verdict() -> None:
    controls = _report()["result_controls"]
    assert controls["descriptive_label_tally"] == {
        "CLEARLY COMPATIBLE": 6,
        "LIKELY COMPATIBLE": 7,
        "LIKELY INCOMPATIBLE": 1,
        "CLEARLY INCOMPATIBLE": 0,
        "UNRESOLVED": 5,
        "OUTSIDE FROZEN SCOPE": 3,
    }
    boundary = _report()["claim_boundary"]
    assert boundary["labels_are_research_judgments_only"] is True
    assert boundary["labels_map_to_V2_statuses"] is False
    assert boundary["V2_population_permitted"] is False
    assert boundary["authoritative_family_judgments_made"] is False


def test_every_surveyed_cell_exposes_reasoning_and_limited_scope() -> None:
    forms = _report()["survey_form_contract"]["forms"]
    surveyed = [row for row in forms if row["workflow_state"] == "SURVEYED_PROVISIONAL"]
    for row in surveyed:
        assert row["concise_rationale"]
        assert row["assumptions_and_domain"]
        assert row["source_or_derivation_pointers"]
        assert row["main_uncertainty"]
        assert row["resolving_calculation_or_theorem"]
        assert row["manual_adjudicator_id"] == survey.ADJUDICATOR_ID
        assert row["manual_review_status"] == "PENDING_INDEPENDENT_RESULT_REVIEW"


def test_sources_are_declared_but_do_not_self_validate_meaning() -> None:
    report = _report()
    source_register = report["source_register"]
    declared = {row["source_id"] for row in source_register["rows"]}
    assert declared == set(survey.SOURCE_CATALOG)
    assert source_register["custody_confers_scientific_relevance"] is False
    assert source_register["special_case_generalizes_to_family"] is False
    for row in report["survey_form_contract"]["forms"]:
        for pointer in row["source_or_derivation_pointers"]:
            assert pointer["reference"] in declared
            assert pointer["scope_note"]


def test_outside_scope_is_not_physical_elimination() -> None:
    forms = {
        row["cell_id"]: row for row in _report()["survey_form_contract"]["forms"]
    }
    expected = {
        "EXP_R2_METRIC_ONLY__F_EXTRA_FIELD",
        "EXP_R2_METRIC_ONLY__F_CONNECTION_TORSION",
        "EXP_R3_LOCALITY__F_NONLOCAL",
    }
    observed = {
        cell_id for cell_id, row in forms.items()
        if row["provisional_classification"] == "OUTSIDE FROZEN SCOPE"
    }
    assert observed == expected
    assert all("not a physical no-go" in " ".join(forms[cell_id]["assumptions_and_domain"]).lower() or
               "no judgment of physical viability" in " ".join(forms[cell_id]["assumptions_and_domain"]).lower()
               for cell_id in expected)


def test_equivalence_probe_is_property_scoped_and_merges_nothing() -> None:
    forms = {
        row["cell_id"]: row for row in _report()["survey_form_contract"]["forms"]
    }
    row = forms["EXP_R6_LOCAL_VARIATION__F_EQUIVALENCE_PROBE"]
    assert row["provisional_classification"] == "CLEARLY COMPATIBLE"
    assert "compact-support local bulk variation" in row["concise_rationale"]
    assert "not transported automatically" in row["main_uncertainty"]
    scope = _report()["scope"]
    assert scope["real_family_equivalence_established"] is False


def test_opportunity_map_selects_one_derivation_not_one_theory() -> None:
    opportunity = _report()["opportunity_map"]
    assert opportunity["native_discriminator_found"] is False
    next_work = opportunity["highest_value_next_bounded_derivation"]
    assert "alpha R^2" in next_work["comparison_instrument"]
    assert "beta R_mn R^mn" in next_work["comparison_instrument"]
    assert len(next_work["tasks"]) == 5
    assert next_work["project_action_proposal"] is False
    assert next_work["authority"] == "EXPLORATORY_RECOMMENDATION_ONLY"
    no_go = opportunity["best_bounded_no_go_or_counterexample_test"]
    assert no_go["theorem_established"] is False
    assert no_go["authority"] == "EXPLORATORY_TEST_RECOMMENDATION_ONLY"


def test_tool_has_no_v2_evaluator_or_scientific_selector_path() -> None:
    path = REPO_ROOT / "formal/python/tools/exploratory_native_gravitational_requirements_family_survey_v0.py"
    source = path.read_text(encoding="utf-8")
    tree = ast.parse(source)
    function_names = {
        node.name for node in tree.body if isinstance(node, ast.FunctionDef)
    }
    assert "evaluate_analysis(" not in source
    assert "action_selection_packet_v2" not in source
    assert not any(
        token in name.lower()
        for name in function_names
        for token in ("survivor", "classifier", "equivalence_reducer", "recommend_theory")
    )


def test_all_eight_result_controls_pass() -> None:
    controls = _report()["result_controls"]
    assert controls["control_count"] == controls["pass_count"] == 8
    assert controls["failure_count"] == 0
    assert all(row["passed"] for row in controls["rows"])


def test_scope_stops_before_authoritative_gravity_work() -> None:
    scope = _report()["scope"]
    assert scope["manual_exploratory_survey_executed"] is True
    assert scope["decision_critical_questions_answered"] == 8
    assert scope["provisional_survey_cells_completed"] == 22
    assert scope["NOT_SURVEYED_cells_retained"] == 48
    assert scope["authoritative_V2_matrix_cells_computed"] == 0
    for key in (
        "authoritative_family_judgments_made",
        "real_family_equivalence_established",
        "authoritative_survivor_computation_executed",
        "native_gravitational_principle_identified",
        "new_postulate_authorized",
        "gravitational_action_selected_or_proposed",
        "matter_sector_selected",
        "metric_or_tetrad_variation_executed",
        "tensor_field_equation_derived",
        "frame_dragging_reopened",
        "automated_action_selection_lane_reopened",
        "automatic_V3_authorized",
    ):
        assert scope[key] is False, key


def test_human_survey_records_questions_cells_opportunity_and_stop() -> None:
    text = (REPO_ROOT / survey.HUMAN_SURVEY_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        survey.VERDICT,
        "DQ1",
        "DQ8",
        "22 / 70",
        "48 / 70",
        "0 / 70",
        "Explicit `NOT_SURVEYED` inventory",
        "Highest-value next bounded derivation",
        "Best bounded no-go/counterexample test",
        "This is a proposed test, not a no-go theorem.",
        survey.SELECTED_NEXT_TARGET,
    ):
        assert token in text
