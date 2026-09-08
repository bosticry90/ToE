from __future__ import annotations

import json
import math
from pathlib import Path

import mpmath as mp

from formal.python.tools import (
    scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0 as execution,
)


ROOT = Path(__file__).resolve().parents[3]


def _synthetic_case() -> dict[str, object]:
    return {
        "case_id": "NONDECISION_SYNTHETIC_TEST",
        "radius_1_m": 0.001,
        "radius_2_m": 0.0015,
        "surface_gap_m": 0.02,
        "center_distance_m": 0.0225,
        "lambda_m": 0.004,
    }


def test_frozen_review_custody_and_single_execution_authority() -> None:
    review, packet = execution._authority_check()
    assert review["verdict"] == "KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_CONTRACT_READY"
    assert review["selected_next_target"] == execution.TARGET
    assert review["authority"]["authorized_diagnosis_execution_count"] == 1
    assert review["authority"]["performed_diagnosis_execution_count"] == 0
    assert len(packet["diagnostic_domain"]["rows"]) == 39


def test_stable_scaled_form_factor_matches_independent_binary64_implementation() -> None:
    for value in (mp.mpf("1e-5"), mp.mpf("0.1"), mp.mpf("1"), mp.mpf("20"), mp.mpf("1000")):
        expected = execution.production.scaled_uniform_sphere_form_factor(float(value))
        actual = float(execution._analytic_h_mp(value))
        assert math.isclose(actual, expected, rel_tol=2e-14, abs_tol=1e-16)


def test_reduced_radial_tanh_sinh_agrees_with_closed_form_on_synthetic_values() -> None:
    with mp.workdps(80):
        for value in (mp.mpf("0.25"), mp.mpf("2"), mp.mpf("12")):
            direct = execution._analytic_h_mp(value)
            radial = execution._radial_h_mp(value)
            assert abs(direct - radial) <= mp.mpf("1e-40") + mp.mpf("1e-20") * abs(direct)


def test_local_tanh_sinh_rules_are_symmetric_and_constant_exact() -> None:
    for count in (1, 3, 5, 7):
        nodes, weights = execution._tanh_sinh_rule(count)
        assert len(nodes) == len(weights) == count
        assert abs(mp.fsum(weights) - 2) < mp.mpf("1e-40")
        assert all(nodes[index] == -nodes[-index - 1] for index in range(count))
        assert all(weight > 0 for weight in weights)


def test_direct_four_coordinate_region_is_finite_on_nondecision_synthetic_case() -> None:
    bounds = (
        (mp.mpf(0), mp.mpf(1)),
        (mp.mpf(-1), mp.mpf(1)),
        (mp.mpf(0), mp.mpf(1)),
        (mp.mpf(-1), mp.mpf(1)),
    )
    with mp.workdps(40):
        newtonian, yukawa, evaluations = execution._direct_region_estimate(
            _synthetic_case(), bounds, 3
        )
    assert newtonian > 0
    assert yukawa > 0
    assert yukawa < newtonian
    assert evaluations == 3**4


def test_fixed_production_density_path_handles_both_components_separately() -> None:
    case = _synthetic_case()
    result = execution._fixed_density_integral(case, 12, profile=True)
    oracle = execution._analytic_oracle(case, radial=False, digits=80)
    assert result["newtonian_J"] < 0
    assert result["yukawa_J"] < 0
    assert execution._relative_error(result["newtonian_J"], oracle["newtonian_J"]) < 1e-8
    assert len(result["profile_bins"]) == 4
    assert math.isclose(
        sum(row["absolute_fraction"] for row in result["profile_bins"]),
        1.0,
        rel_tol=1e-14,
    )


def test_exact_analytic_dft_and_alias_controls_pass() -> None:
    rows, analytic_pass, alias_pass = execution._analytic_dft_diagnostics()
    assert analytic_pass is True
    assert alias_pass is True
    assert len(rows) == 20


def test_execution_result_is_bounded_when_present() -> None:
    report_path = ROOT / execution.REPORT_RELATIVE_PATH
    if not report_path.exists():
        return
    report = json.loads(report_path.read_text(encoding="utf-8"))
    assert report["target"] == execution.TARGET
    assert report["authority"]["consumed_diagnosis_execution_count"] == 1
    assert report["selected_next_target"] == execution.SELECTED_NEXT_TARGET
    assert report["scope"]["production_kernel_changed"] is False
    assert report["scope"]["integration_method_replaced"] is False
    assert report["scope"]["stage_a_rerun_performed"] is False
    assert report["scope"]["final_real_150_vector_produced"] is False
    assert report["scope"]["jacobian_computed"] is False
    assert report["scope"]["physical_identifiability_evaluated"] is False
    assert report["scope"]["stage_b_authorized"] is False


def test_timeout_result_fails_closed_without_production_adjudication_when_present() -> None:
    report_path = ROOT / execution.REPORT_RELATIVE_PATH
    if not report_path.exists():
        return
    report = json.loads(report_path.read_text(encoding="utf-8"))
    assert report["status"] == (
        "COMPLETED_ONCE_FAIL_CLOSED_TOTAL_WORK_CAP_PENDING_INDEPENDENT_RESULT_REVIEW"
    )
    assert report["principal_outcome"] == "REFERENCE_ORACLE_INADEQUATE"
    assert report["principal_labels"] == ["REFERENCE_ORACLE_INADEQUATE"]
    assert report["oracle_availability_outcome"] == (
        "ANALYTIC_OR_REDUCED_SPHERE_ORACLE_NOT_VALIDATED"
    )
    assert report["execution_summary"]["reference_plateau_established"] is False
    assert report["execution_summary"]["production_path_judged_against_accepted_oracle"] is False
    evidence = report["execution_summary"]["root_cause"]["predicate_evidence"]
    assert evidence["launcher_exit_code"] == 124
    assert evidence["launcher_reported_wall_time_seconds"] == 3604.1
    assert evidence["frozen_total_wall_clock_cap_seconds"] == 3600
    assert evidence["scientific_rerun_performed"] is False
    assert report["artifact_manifest"]["artifact_count"] == 1


def test_one_run_guard_checks_both_canonical_result_locations() -> None:
    source = Path(execution.__file__).read_text(encoding="utf-8")
    assert "single bounded diagnosis execution authority is already consumed" in source
    assert "output_result_path.exists()" in source
    assert "report_path.exists()" in source


def test_forbidden_scientific_outputs_are_absent_from_executor_schema() -> None:
    source = Path(execution.__file__).read_text(encoding="utf-8")
    assert '"final_real_150_vector_produced": False' in source
    assert '"jacobian_computed": False' in source
    assert '"eta_lambda_computed": False' in source
    assert '"sensitivity_forecast_produced": False' in source
    assert '"stage_b_authorized": False' in source
