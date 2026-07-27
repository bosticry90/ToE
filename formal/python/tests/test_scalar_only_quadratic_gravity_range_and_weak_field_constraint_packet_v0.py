from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_v0
    as packet,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / packet.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _rows(section: str, id_key: str) -> dict[str, dict[str, object]]:
    return {row[id_key]: row for row in _report()[section]["rows"]}


def test_packet_regenerates_and_preserves_frozen_authority() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in packet.AUTHORITY_HASHES}
    packet.build_packet()
    after = {path: _sha256(REPO_ROOT / path) for path in packet.AUTHORITY_HASHES}
    assert before == after == packet.AUTHORITY_HASHES


def test_exact_response_authority_is_consumed_and_review_is_next() -> None:
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["authority"]["consumed_response_selection_verdict"] == (
        "SELECTED_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_PREPARATION"
    )
    assert report["authority"]["consumed_candidate_id"] == (
        "BOUND_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_PHENOMENOLOGY"
    )
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == packet.SELECTED_NEXT_TARGET_KIND


def test_fixed_scalar_model_and_si_maps_do_not_select_alpha() -> None:
    model = _report()["comparison_model"]
    assert model["status"] == "SUPPLIED_SCALAR_ONLY_QUADRATIC_GRAVITY_COMPARISON"
    assert model["fixed_yukawa_amplitude"] == "A_Y=1/3"
    assert model["range"] == "lambda0=sqrt(-6 alpha_packet)>0"
    assert model["alpha_map"] == "alpha_packet=-lambda0^2/6<0"
    assert model["inverse_length_mass"] == "m0=1/lambda0 [m^-1]"
    assert model["particle_mass"] == "M0=hbar/(c lambda0) [kg]"
    assert model["alpha_value_or_bound_selected"] is False
    assert model["scalar_branch_adopted"] is model["toe_native"] is False


def test_one_primary_observable_is_selected_and_two_are_deferred() -> None:
    selection = _report()["observable_selection"]
    rows = _rows("observable_selection", "candidate_id")
    assert selection["candidate_count"] == len(rows) == 3
    assert selection["selected_primary_count"] == 1
    assert selection["cross_check_selected"] is False
    assert rows["EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE"][
        "disposition"
    ] == "SELECTED_FOR_PACKET_CONTRACT_ONLY"
    assert rows["VECTOR_FORCE_SENSOR_2024_2026"]["disposition"] == (
        "DEFERRED_INSUFFICIENT_FIXED_AMPLITUDE_SENSITIVITY"
    )
    assert rows["SOLAR_SYSTEM_ORBITAL_WEAK_FIELD_CLASS"]["disposition"] == (
        "DEFERRED_TRANSPORT_AND_DEGENERACY_UNRESOLVED"
    )


def test_primary_contract_freezes_measurements_and_nuisances_without_analysis() -> None:
    primary = _report()["selected_primary_contract"]
    assert primary["measurement_settings"] == 95
    assert primary["harmonics"] == ["18 omega", "54 omega", "120 omega"]
    assert primary["measurement_count"] == 285
    assert primary["experimental_parameter_count"] == 17
    assert primary["profiled_nuisance_count"] == 5
    assert len(primary["profiled_nuisances"]) == 5
    assert primary["published_generic_limit_is_packet_result"] is False
    assert primary["real_data_analysis_authorized"] is False


def test_transport_uses_extended_sources_and_one_harmonic_torque_path() -> None:
    transport = _report()["theory_to_observable_transport"]
    assert "A_Y (1+r/lambda0)" in transport["point_source_radial_acceleration"]
    assert "rho_D(x) rho_A(x')" in transport["extended_source_yukawa_energy"]
    assert transport["measured_torque"] == "N_Y(phi)=-partial U_Y/partial phi"
    assert transport["point_mass_approximation_allowed"] is False
    assert "Newtonian and fixed-amplitude Yukawa" in transport[
        "required_implementation"
    ]
    assert transport["transport_executed"] is False


def test_extended_source_inputs_and_validity_gate_are_explicit() -> None:
    source = _report()["extended_source_contract"]
    assert len(source["required_inputs"]) == 10
    assert "detector and attractor density masks" in source["required_inputs"]
    assert "point-source" not in source["point_source_validity_criterion"].lower()
    assert "quantified form-factor error" in source["point_source_validity_criterion"]
    assert source["geometry_model_available_for_execution"] is False


def test_public_data_audit_fails_closed_without_claiming_data_do_not_exist() -> None:
    audit = _report()["primary_data_audit"]
    rows = _rows("primary_data_audit", "item_id")
    assert audit["row_count"] == len(rows) == 7
    assert audit["execution_sufficient_count"] == 0
    assert rows["SUPPLEMENTAL_MATERIAL"]["status"] == (
        "IDENTIFIED_BUT_NOT_INGESTED"
    )
    assert rows["PRIMARY_NUMERICAL_MEASUREMENT_VECTOR"]["status"] == (
        "NOT_OBTAINED_AND_FROZEN"
    )
    assert audit["machine_readable_measurement_vector_frozen"] is False
    assert audit["complete_uncertainty_model_frozen"] is False
    assert audit["executable_extended_source_model_frozen"] is False
    assert audit["provisional_block"] == packet.PROVISIONAL_READINESS


def test_generic_published_limit_cannot_become_fixed_one_third_result() -> None:
    row = _rows("primary_data_audit", "item_id")[
        "PUBLISHED_GENERIC_YUKAWA_LIMIT"
    ]
    assert row["status"] == "AVAILABLE_AS_POST_EXECUTION_ORACLE_ONLY"
    assert "not the fixed A_Y=1/3 result" in row["detail"]


def test_calibration_and_long_range_degeneracies_are_retained() -> None:
    degeneracy = _report()["degeneracy_contract"]
    short = degeneracy["primary_short_range"]
    long = degeneracy["deferred_long_range"]
    assert short["torque_scale"] == "PROFILE_GAMMA_WITH_PRIMARY_GAUSSIAN_PRIOR"
    assert short["separation_and_centering"] == (
        "PROFILE_X0_Y0_S0_WITH_PRIMARY_PRIORS"
    )
    assert "4/3 rescaling" in long["lambda_much_greater_than_r"]
    assert long["status"] == "DEFERRED_NO_EPHEMERIS_OR_GM_COVARIANCE_FROZEN"


def test_statistical_rule_profiles_nuisances_and_calibrates_boundary_coverage() -> None:
    stats = _report()["statistical_contract"]
    assert stats["analysis_status"] == "PREREGISTERED_STRUCTURE_NOT_EXECUTABLE"
    assert stats["physical_parameters"] == ["lambda0>0 with fixed A_Y=1/3"]
    assert stats["nuisance_rule"] == (
        "profile all five primary nuisances at every lambda0"
    )
    assert "do not assume a textbook Delta-chi-square law" in stats["boundary_rule"]
    assert "parametric bootstrap" in stats["boundary_rule"]
    assert "complete connected or disconnected allowed lambda0 set" in stats[
        "allowed_set_rule"
    ]
    assert stats["combination_rule"] == "NO_DATASET_COMBINATION_IN_V0"
    assert stats["numerical_threshold_selected"] is False


def test_si_conversion_preserves_mass_meanings_and_finite_data_limit() -> None:
    si = _report()["si_conversion_contract"]
    assert si["m0"] == "1/lambda0 in inverse metres"
    assert si["M0"] == "hbar/(c lambda0) in kilograms"
    assert si["alpha_packet"] == "-lambda0^2/6 in square metres"
    assert si["allowed_range_translation"] == (
        "if 0<lambda0<lambda_max, then -lambda_max^2/6<alpha_packet<0"
    )
    assert si["exact_alpha_zero_from_finite_data_licensed"] is False


def test_future_controls_are_frozen_but_none_has_run() -> None:
    controls = _report()["future_execution_controls"]
    assert controls["control_count"] == len(controls["rows"]) == 9
    assert controls["executed_count"] == 0
    assert "A_Y_to_zero_software_null" in controls["rows"]
    assert "synthetic_fixed_amplitude_signal_recovery" in controls["rows"]
    assert "synthetic_null_coverage" in controls["rows"]


def test_all_unblock_requirements_are_required_and_none_is_preclaimed() -> None:
    unblock = _report()["unblock_requirements"]
    assert unblock["requirement_count"] == len(unblock["rows"]) == 5
    assert unblock["all_required"] is True
    assert unblock["satisfied_count"] == 0
    assert any("95x3" in row for row in unblock["rows"])
    assert any("published Newtonian baseline" in row for row in unblock["rows"])


def test_packet_outcomes_keep_provisional_block_reviewable() -> None:
    outcomes = _report()["outcome_contract"]
    assert tuple(outcomes["packet_review_outcomes"]) == packet.PACKET_REVIEW_OUTCOMES
    assert outcomes["provisional_packet_review_outcome"] == (
        "BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE"
    )
    assert outcomes[
        "independent_review_may_upgrade_to_ready_only_if_all_unblock_requirements_pass"
    ] is True
    assert outcomes["future_numerical_outcome"] is None


def test_twenty_preparation_controls_pass() -> None:
    controls = _report()["preparation_controls"]
    assert controls["control_count"] == controls["pass_count"] == 20
    assert controls["failure_count"] == 0
    assert all(row["passed"] for row in controls["rows"])


def test_scope_stops_before_data_analysis_and_theory_adoption() -> None:
    scope = _report()["scope"]
    assert scope["packet_preparation_executed"] is True
    assert scope["primary_dataset_selected_for_contract_audit"] is True
    assert scope["primary_data_custody_complete"] is False
    for key, value in scope.items():
        if key in {
            "packet_preparation_executed",
            "primary_dataset_selected_for_contract_audit",
            "primary_data_custody_complete",
        }:
            continue
        assert value is False, key

