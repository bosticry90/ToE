from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_packet_review_v0
    as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_packet_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES


def test_principal_result_blocks_execution_without_claiming_physical_failure() -> None:
    report = _report()
    assert report["principal_packet_review_outcome"] == "BLOCKED_PARAMETER_IDENTIFIABILITY"
    assert report["execution_readiness"] == "NOT_READY"
    assert report["jacobian_contract_review"]["physical_identifiability_evaluated"] is False
    assert report["scope"]["deterministic_execution_authorized"] is False


def test_harmonic_convention_and_real_vector_are_independently_verified() -> None:
    harmonic = _report()["independent_harmonic_review"]
    assert harmonic["a_n_relation"] == "a_n=2*Re(c_n)"
    assert harmonic["b_n_relation"] == "b_n=-2*Im(c_n)"
    assert harmonic["real_vector_length"] == 150
    assert harmonic["real_vector_order"] == "GAP_MAJOR_2RE_2IM_4RE_4IM_6RE_6IM"
    assert harmonic["complete"] is True


def test_geometry_torque_symmetry_and_label_swaps_are_coherent() -> None:
    geometry = _report()["independent_geometry_and_torque_review"]
    assert geometry["energy_pi_periodic"] is True
    assert geometry["energy_even"] is True
    assert geometry["torque_odd"] is True
    assert geometry["equal_body_label_swap_invariant"] is True
    assert geometry["complete"] is True


def test_production_benchmarks_mutations_and_cross_checks_pass_contract_review() -> None:
    production = _report()["production_and_control_review"]
    assert production["shared_function_count"] == 6
    assert production["benchmark_count"] == 4
    assert production["mutation_count"] == 5
    assert production["independent_torque_cross_check_count"] == 2
    assert production["production_side_shared"] is True
    assert production["reference_density_cubature_independent"] is True


def test_sixteen_maps_and_exact_amplitude_degeneracy_are_verified() -> None:
    perturbations = _report()["perturbation_review"]
    assert perturbations["count"] == 16
    assert perturbations["composition_order_complete"] is True
    assert perturbations["exact_amplitude_degeneracy"] == [
        "TORQUE_CALIBRATION",
        "SOURCE_DENSITY_SCALE",
        "DETECTOR_DENSITY_SCALE",
    ]
    assert perturbations["separately_data_identifiable"] is False


def test_four_jacobian_interfaces_are_incomplete() -> None:
    jacobian = _report()["jacobian_contract_review"]
    assert jacobian["row_count"] == 150
    assert jacobian["column_count"] == 17
    assert jacobian["parameter_order_complete"] is True
    assert jacobian["numeric_base_steps_complete"] is False
    assert jacobian["rank_deficient_projector_policy_complete"] is False
    assert jacobian["transition_domain_complete"] is False
    assert jacobian["refinement_acceptance_tolerances_complete"] is False
    assert jacobian["complete"] is False


def test_exact_four_diagnostics_and_unblock_requirements() -> None:
    report = _report()
    assert report["diagnostics"] == list(review.DIAGNOSTICS)
    assert len(report["unblock_requirements"]) == 4
    assert all(row["satisfied"] is False for row in report["unblock_requirements"])


def test_twenty_four_gates_have_four_failures() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 24
    assert gates["pass_count"] == 20
    assert gates["failure_count"] == 4
    failed = [row["gate_id"] for row in gates["rows"] if row["status"] == "FAIL"]
    assert failed == [
        "G18_JACOBIAN_FINITE_DIFFERENCE_STEPS",
        "G20_RANK_DEFICIENT_NUISANCE_PROJECTOR",
        "G21_TRANSITION_DOMAIN_EXACTNESS",
        "G22_IDENTIFIABILITY_REFINEMENT_STABILITY",
    ]


def test_scope_allows_review_findings_only() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "independent_packet_review_executed",
        "harmonic_and_real_150_contract_verified",
        "shared_kernel_and_torque_contract_verified",
        "benchmark_mutation_and_symmetry_contract_verified",
        "deterministic_perturbation_maps_verified",
        "exact_amplitude_degeneracy_verified",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_review_records_block_and_next_authority() -> None:
    text = (REPO_ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "20 / 24 PASSED",
        "not a finding that the apparatus is physically",
        "150",
        "NOT AUTHORIZED",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
