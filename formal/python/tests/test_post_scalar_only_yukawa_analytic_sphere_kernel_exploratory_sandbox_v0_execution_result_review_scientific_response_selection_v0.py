from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    post_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v0_execution_result_review_scientific_response_selection_v0
    as selector,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selector.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selector_regenerates_and_pins_accepted_failure_review() -> None:
    assert selector.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selector.TARGET
    assert report["verdict"] == selector.VERDICT
    assert report["selected_route"] == selector.SELECTED_ROUTE
    assert report["selected_next_target"] == selector.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_review_artifacts"]
    } == selector.REVIEW_HASHES


def test_review_interpretation_is_exact_and_non_scientific() -> None:
    interpretation = _report()["review_interpretation"]
    assert interpretation["review_verdict"] == (
        "ACCEPTED_EXPLORATORY_IMPLEMENTATION_SERIALIZATION_FAILURE"
    )
    assert interpretation["review_pass_count"] == 40
    assert interpretation["contract_ambiguous"] is False
    assert interpretation["implementation_defect_localized"] is True
    assert interpretation["analytic_oracle_remains_qualified"] is True
    assert interpretation["sandbox_kernel_qualified_or_refuted"] is False
    assert interpretation["transient_values_admissible"] is False


def test_selector_has_exactly_two_options_and_v1_wins() -> None:
    report = _report()
    assert report["selection_policy"]["candidate_count"] == 2
    assert report["selection_policy"]["options_exact"] == list(
        selector.EXACT_SELECTOR_OPTIONS
    )
    ranking = report["ranking"]
    assert ranking["selected_candidate_id"] == selector.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 270
    assert ranking["runner_up_score"] == 195
    assert ranking["winning_margin"] == 75
    assert report["sensitivity_analysis"]["variant_count"] == 33
    assert report["sensitivity_analysis"][
        "selected_candidate_stable_in_all_variants"
    ] is True


def test_v0_source_and_scientific_surfaces_are_frozen() -> None:
    contract = _report()["v1_change_contract"]
    assert contract["base_v0_source_sha256"] == selector.V0_SOURCE_SHA256
    assert len(contract["permitted_change_classes"]) == 7
    assert len(contract["frozen_scientific_surfaces"]) == 13
    assert contract["permissive_json_default_forbidden"] is True
    assert contract["source_diff_outside_permitted_classes_fails_closed"] is True


def test_real_path_serialization_control_and_atomic_commit_are_mandatory() -> None:
    control = _report()["real_path_serialization_control"]
    assert control["runs_before_decision_bearing_calculations"] is True
    assert control["schema_complete_synthetic_final_aggregate"] is True
    assert control["all_live_decimal_locations_populated"] is True
    assert control["same_finalization_path_as_real_result"] is True
    assert control["failure_consumes_execution_and_fails_closed"] is True
    assert control["atomic_commit_pipeline"] == list(selector.ATOMIC_COMMIT_PIPELINE)


def test_one_shot_terminal_outcomes_are_exclusive() -> None:
    terminal = _report()["terminal_boundary"]
    assert terminal["authorized_v1_execution_count"] == 1
    assert terminal["automatic_v2_authorized"] is False
    assert terminal["additional_repair_chain_authorized"] is False
    assert terminal["additional_infrastructure_prerequisite_authorized"] is False
    assert terminal["preservation_failure_successor"] == (
        "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE_ONLY"
    )
    assert terminal["complete_result_successor"] == (
        "INDEPENDENT_EXPLORATORY_RESULT_REVIEW_ONLY"
    )


def test_scope_rotates_authority_without_implementation_or_science() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "scientific_response_selection_executed",
        "accepted_failure_review_frozen",
        "final_v1_sandbox_implementation_authorized",
        "one_v1_sandbox_execution_authorized",
    }
    assert scope["v1_sandbox_implemented_now"] is False
    assert scope["v1_sandbox_executed_now"] is False
    assert scope["production_change_authorized"] is False
    assert scope["historical_cubature_adjudication_authorized"] is False
    assert scope["shadow_qualification_authorized"] is False
    assert scope["scientific_claim_authorized"] is False


def test_human_selector_records_boundary_and_current_authority() -> None:
    text = (ROOT / selector.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selector.VERDICT,
        selector.SELECTED_ROUTE,
        "270",
        "195",
        "33 / 33",
        selector.V0_SOURCE_SHA256,
        "json.dumps(..., default=str)",
        "No V1 implementation was created or executed by this selector",
        selector.SELECTED_NEXT_TARGET,
    ):
        assert token in text
