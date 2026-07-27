from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    post_quadratic_gravity_comparison_conditional_mode_selection_envelope_v0 as execution,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / execution.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _row(selector_id: str) -> dict[str, object]:
    return next(
        row for row in _report()["selector_adjudication"]["rows"]
        if row["selector_id"] == selector_id
    )


def test_execution_regenerates_exactly_and_consumes_one_authorized_run() -> None:
    assert execution.artifact_bytes() == execution.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == execution.TARGET
    assert report["verdict"] == execution.VERDICT
    assert report["selected_next_target"] == execution.SELECTED_NEXT_TARGET
    assert report["authority"]["authorized_execution_count"] == 1
    assert report["authority"]["consumed_execution_count"] == 1
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_review_artifacts"]
    } == execution.REVIEW_HASHES


def test_all_ten_selectors_use_shared_path_and_are_not_adopted() -> None:
    register = _report()["selector_adjudication"]
    assert register["selector_count"] == register["adjudicated_count"] == 10
    assert register["adopted_count"] == 0
    assert all(
        row["adjudication_status"]
        == "AUTHORITY_CLASSIFIED_CONSEQUENCE_RECORDED_NOT_ADOPTED"
        for row in register["rows"]
    )
    assert all(row["scope"] == "FROZEN_QUADRATIC_COMPARISON_SCOPE" for row in register["rows"])
    assert all(row["condition_adopted"] is False for row in register["rows"])


def test_each_selector_exposes_required_classification_fields() -> None:
    for row in _report()["selector_adjudication"]["rows"]:
        for field in (
            "selector_condition",
            "canonical_provenance",
            "conditional_parameter_consequence",
            "consequence_kind",
            "remaining_mode_content",
            "scope",
            "unresolved_scientific_obligation",
            "adoption_status",
        ):
            assert row[field]


def test_R9_and_R10_remain_native_evaluation_obligations_without_selection() -> None:
    r9 = _row("SEL_NATIVE_R9_CURRENT_REPRESENTABILITY")
    r10 = _row("SEL_NATIVE_R10_STABILITY_EVALUATION")
    assert r9["conditional_parameter_consequence"] == "NONE_BY_ITSELF"
    assert r10["conditional_parameter_consequence"] == "NONE_WITHOUT_AN_ACCEPTANCE_THRESHOLD"
    for row in (r9, r10):
        assert row["canonical_provenance"]["authority_class"] == "PROJECT_BOUND_NATIVE_PRINCIPLE"
        assert row["canonical_provenance"]["authority_effect"] == "PROJECT_AUTHORITY_SUPPORTS_EVALUATION_ONLY"
        assert row["native_branch_selection_authority"] is False


def test_standard_stability_criteria_remain_supplied_and_conditional() -> None:
    tachyon = _row("SEL_NO_TACHYONIC_POLES")
    ghost = _row("SEL_NO_NEGATIVE_RESIDUE_SPIN2")
    assert tachyon["conditional_parameter_consequence"] == "Sigma<0 and beta>0 when both extra poles are present"
    assert "NEGATIVE_RESIDUE_SPIN2" in tachyon["remaining_mode_content"]
    assert ghost["conditional_parameter_consequence"] == "beta=0"
    assert ghost["remaining_mode_content"] == "MASSLESS_SPIN2_PLUS_POSSIBLE_SCALAR"
    for row in (tachyon, ghost):
        assert row["canonical_provenance"]["authority_class"] == "SUPPLIED_STANDARD_PHYSICS_CRITERION"
        assert row["condition_adopted"] is False


def test_minimal_mode_condition_collapses_family_only_conditionally() -> None:
    minimal = _row("SEL_MINIMAL_SPECTRUM")
    assert minimal["canonical_provenance"]["authority_binding"] == "S3_NO_EXTRA_GRAVITATIONAL_MODES"
    assert minimal["canonical_provenance"]["authority_class"] == "SUPPLIED_STANDARD_PHYSICS_CRITERION"
    assert minimal["conditional_parameter_consequence"] == "beta=0 and Sigma=0 implies alpha=beta=0"
    assert minimal["remaining_mode_content"] == "MASSLESS_SPIN2_ONLY"
    assert minimal["condition_adopted"] is False


def test_exact_and_finite_precision_current_results_remain_disjoint() -> None:
    exact = _row("SEL_EXACT_EINSTEIN_0I")
    empirical = _row("SEL_FINITE_PRECISION_0I")
    assert exact["conditional_parameter_consequence"] == "beta=0"
    assert empirical["consequence_kind"] == "EMPIRICAL_BOUND_NOT_EXACT_IDENTITY"
    assert "beta=0 not logically inferred" in empirical["conditional_parameter_consequence"]
    classification = _report()["exact_empirical_current_classification"]
    assert classification["exact_beta_zero_from_finite_data_licensed"] is False
    assert classification["dataset_imported"] is False


def test_hypothetical_postulate_remains_uncreated_and_unadopted() -> None:
    row = _row("SEL_HYPOTHETICAL_MINIMAL_MODE_POSTULATE")
    assert row["canonical_provenance"]["authority_class"] == "PROPOSED_NEW_POSTULATE"
    assert row["canonical_provenance"]["authority_effect"] == "HYPOTHETICAL_REQUIRES_FRESH_AUTHORITY"
    assert row["condition_adopted"] is False
    assert row["native_branch_selection_authority"] is False


def test_principal_classifier_has_three_exclusive_paths() -> None:
    rows = _report()["selector_adjudication"]["rows"]
    assert execution.classify_principal(rows, authority_complete=True, logic_scope_valid=True) == "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE"
    assert execution.classify_principal(rows, authority_complete=False, logic_scope_valid=True) == "CONDITIONAL_MODE_SELECTION_ENVELOPE_BLOCKED_AUTHORITY"
    assert execution.classify_principal(rows, authority_complete=True, logic_scope_valid=False) == "CONDITIONAL_MODE_SELECTION_ENVELOPE_BLOCKED_LOGIC_OR_SCOPE"


def test_one_principal_outcome_and_all_subordinate_findings_are_issued() -> None:
    report = _report()
    principal = report["principal_classification"]
    assert principal["outcome"] == execution.VERDICT
    assert principal["outcome_count"] == 1
    assert principal["native_selector_count"] == 0
    assert tuple(report["subordinate_findings"]) == execution.SUBORDINATE_FINDINGS


def test_all_three_positions_remain_open_and_unselected() -> None:
    positions = _report()["position_map"]
    assert positions["position_count"] == 3
    assert positions["selected_count"] == 0
    assert all(row["selected"] is False for row in positions["rows"])
    assert positions["rows"][2]["status"] == "OPEN_NOT_SELECTED_FRESH_TARGET_REQUIRED"


def test_coincident_mass_surface_does_not_repair_spin2_channel() -> None:
    coincident = _report()["coincident_mass_status"]
    assert coincident["pole_locations_coincide"] is True
    assert coincident["P2_P0s_orthogonal"] is True
    for key in ("double_pole", "mode_merger", "cancellation", "ghost_repaired"):
        assert coincident[key] is False


def test_all_eighteen_execution_controls_pass_shared_path() -> None:
    controls = _report()["execution_controls"]
    assert controls["control_count"] == controls["pass_count"] == 18
    assert controls["failure_count"] == 0
    assert all(row["status"] == "PASSED" for row in controls["rows"])
    assert all(row["uses_shared_execution_path"] is True for row in controls["rows"])


def test_scope_records_execution_but_forbids_every_scientific_promotion() -> None:
    scope = _report()["scope"]
    assert scope["authorized_execution_consumed"] == 1
    for key in (
        "envelope_execution_completed",
        "selector_adjudication_completed",
        "principal_classification_issued",
        "independent_result_review_required",
    ):
        assert scope[key] is True
    for key, value in scope.items():
        if key not in {
            "authorized_execution_consumed",
            "envelope_execution_completed",
            "selector_adjudication_completed",
            "principal_classification_issued",
            "independent_result_review_required",
        }:
            assert value is False, key


def test_claim_ceiling_and_human_record_state_exact_stop() -> None:
    report = _report()
    claim = report["claim_ceiling"]
    for token in (
        "No condition",
        "branch",
        "native principle",
        "postulate",
        "gravitational action",
        "outside-family mechanism",
        "dataset",
        "frame-dragging result",
        "V2 cell",
    ):
        assert token in claim
    text = (REPO_ROOT / execution.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        execution.VERDICT,
        "selector records adjudicated:      10 / 10",
        "conditions adopted:                0",
        "18 / 18 PASSED",
        "OPEN_NOT_SELECTED",
        execution.SELECTED_NEXT_TARGET,
    ):
        assert token in text
