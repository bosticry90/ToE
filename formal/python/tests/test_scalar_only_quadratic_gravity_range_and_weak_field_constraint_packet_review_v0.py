from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_review_v0
    as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _gates() -> dict[str, dict[str, object]]:
    return {row["gate_id"]: row for row in _report()["review_gates"]["rows"]}


def test_review_regenerates_exactly_and_preserves_packet_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in review.PACKET_HASHES}
    review.build_review()
    after = {path: _sha256(REPO_ROOT / path) for path in review.PACKET_HASHES}
    assert before == after == review.PACKET_HASHES


def test_review_consumes_exact_packet_and_confirms_principal_block() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["principal_packet_review_outcome"] == (
        "BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE"
    )
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND


def test_primary_source_dimensions_and_fit_structure_are_reproduced() -> None:
    source = _report()["independent_primary_source_reproduction"]
    assert source["measurement_setting_count"] == 95
    assert source["harmonic_count"] == 3
    assert source["measurement_count"] == 285
    assert source["harmonics"] == ["18 omega", "54 omega", "120 omega"]
    assert source["experimental_parameter_count"] == 17
    assert source["profiled_nuisance_count"] == 5
    assert source["published_newtonian_baseline"] == (
        "chi_squared=275.0 for nu=285, P=0.654"
    )


def test_scientific_suitability_and_independent_executability_are_separate() -> None:
    result = _report()["scientific_suitability"]
    assert result["fixed_model_signal"] == "A_Y=1/3"
    assert result["experiment_scientifically_suitable"] is True
    assert result["theory_to_observable_transport_structurally_defined"] is True
    assert result["independent_project_fit_executable"] is False
    assert result["published_result_rejected"] is False


def test_every_missing_item_is_bound_to_a_likelihood_operation() -> None:
    dependency = _report()["decision_bearing_dependency_map"]
    assert dependency["row_count"] == 5
    rows = dependency["rows"]
    assert all(row["required_operation"] for row in rows)
    assert all(row["failure_if_guessed"] for row in rows)
    assert {row["missing_item"] for row in rows} == {
        "COMPLETE_95_BY_3_TORQUE_VECTOR_AND_DISPLACEMENTS",
        "NUMERICAL_UNCERTAINTY_AND_CORRELATION_MODEL",
        "FIVE_NUMERICAL_NUISANCE_PRIORS",
        "VERIFIED_EXTENDED_SOURCE_TORQUE_IMPLEMENTATION",
        "BOUNDARY_AWARE_COVERAGE_CALIBRATION",
    }


def test_principal_and_subordinate_diagnostics_are_exact() -> None:
    diagnostics = _report()["diagnostics"]
    assert diagnostics["principal"] == review.VERDICT
    assert diagnostics["subordinate_count"] == 5
    assert diagnostics["subordinate"] == list(review.DIAGNOSTICS)


def test_all_eight_no_bypass_probes_pass() -> None:
    probes = _report()["adversarial_no_bypass_probes"]
    assert probes["probe_count"] == probes["pass_count"] == 8
    assert all(row["expected"] == row["observed"] == "REJECT" for row in probes["rows"])
    assert all(row["passed"] is True for row in probes["rows"])


def test_supplement_identification_does_not_become_custody() -> None:
    probes = {row["probe_id"]: row for row in _report()["adversarial_no_bypass_probes"]["rows"]}
    assert probes["SUPPLEMENT_EXISTENCE_IS_NOT_CUSTODY"]["passed"] is True


def test_plots_and_generic_curve_cannot_issue_packet_bound() -> None:
    probes = {row["probe_id"]: row for row in _report()["adversarial_no_bypass_probes"]["rows"]}
    assert probes["PLOT_DIGITIZATION_BYPASS"]["passed"] is True
    assert probes["GENERIC_EXCLUSION_CURVE_BYPASS"]["passed"] is True
    scope = _report()["scope"]
    assert scope["published_limit_imported_as_packet_result"] is False


def test_dissertation_remains_supporting_source_only() -> None:
    gate = _gates()["G10_DISSERTATION_REMAINS_SUPPORTING_METHODS_ONLY"]
    assert gate["status"] == "PASS"
    assert "cannot supply missing calibrated numerical evidence" in gate["finding"]


def test_point_source_shortcut_and_approximate_geometry_are_rejected() -> None:
    probes = {row["probe_id"]: row for row in _report()["adversarial_no_bypass_probes"]["rows"]}
    assert probes["POINT_SOURCE_GEOMETRY_BYPASS"]["passed"] is True
    assert _gates()["G9_POINT_SOURCE_APPROXIMATION_REMAINS_FORBIDDEN"]["status"] == "PASS"


def test_uncertainty_and_nuisance_guesses_are_rejected() -> None:
    probes = {row["probe_id"]: row for row in _report()["adversarial_no_bypass_probes"]["rows"]}
    assert probes["DIAGONAL_ERROR_GUESS"]["passed"] is True
    assert probes["REASONABLE_NUISANCE_PRIOR_GUESS"]["passed"] is True
    assert _gates()["G6_UNCERTAINTY_AND_CORRELATION_CONTRACT_INCOMPLETE"]["status"] == "PASS"
    assert _gates()["G7_FIVE_NUISANCE_PRIORS_CANNOT_BE_GUESSED"]["status"] == "PASS"


def test_boundary_threshold_remains_uncalibrated() -> None:
    probes = {row["probe_id"]: row for row in _report()["adversarial_no_bypass_probes"]["rows"]}
    assert probes["ASYMPTOTIC_THRESHOLD_BYPASS"]["passed"] is True
    assert _gates()["G13_BOUNDARY_COVERAGE_REMAINS_UNCALIBRATED"]["status"] == "PASS"


def test_all_eighteen_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 18
    assert gates["failure_count"] == 0
    assert len(_gates()) == 18
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_no_unblock_requirement_has_been_satisfied() -> None:
    block = _report()["execution_block"]
    assert block["unblock_requirement_count"] == 5
    assert block["satisfied_unblock_requirement_count"] == 0
    assert len(block["binding_unblock_requirements"]) == 5


def test_no_fit_or_numerical_bound_is_authorized_or_executed() -> None:
    block = _report()["execution_block"]
    assert block["constraint_execution_authorized"] is False
    assert block["real_data_analysis_executed"] is False
    assert block["likelihood_evaluated"] is False
    assert block["numerical_lambda_bound_computed"] is False
    assert block["numerical_alpha_bound_computed"] is False


def test_future_actions_are_candidates_for_selection_not_automatic_authority() -> None:
    future = _report()["future_response_selection"]
    assert future["automatic_successor_authorized"] is False
    assert future["selection_only"] is True
    assert len(future["candidate_responses"]) == 4
    assert future["selected_response_now"] is None


def test_no_data_acquisition_contact_or_reinterpretation_is_authorized() -> None:
    scope = _report()["scope"]
    assert scope["supplement_acquisition_authorized"] is False
    assert scope["author_contact_authorized"] is False
    assert scope["alternate_experiment_selected"] is False
    assert scope["publication_level_reinterpretation_authorized"] is False


def test_theory_and_downstream_firewalls_remain_closed() -> None:
    scope = _report()["scope"]
    for field in (
        "beta_zero_adopted",
        "alpha_sign_or_value_adopted",
        "scalar_branch_adopted",
        "native_scalar_bridge_identified",
        "native_gravitational_principle_identified",
        "gravitational_action_selected",
        "matter_sector_selected",
        "orbital_or_light_propagation_analysis_executed",
        "frame_dragging_resumed",
        "master_action_mutated",
    ):
        assert scope[field] is False


def test_current_posture_rotates_only_to_scientific_response_selection() -> None:
    posture = _report()["current_posture"]
    assert posture["weak_field_phenomenology_packet_review"] == "BLOCKED"
    assert posture["likelihood"] == "NOT_EXECUTED"
    assert posture["scalar_range_bound"] == "NONE"
    assert posture["alpha"] == "NOT_SELECTED"
    assert posture["scalar_branch"] == "NOT_ADOPTED"
    assert posture["next_authority"] == review.SELECTED_NEXT_TARGET
