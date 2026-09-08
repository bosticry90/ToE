from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0 as execution,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / execution.REPORT_RELATIVE_PATH
HUMAN_PATH = (
    ROOT / "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_20260719_v0.md"
)


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_execution_consumed_exact_authority_once_and_rotated_to_result_review() -> None:
    report = _report()
    assert report["target"] == execution.TARGET
    assert report["principal_result"] == "ANALYTIC_SPHERE_ORACLE_QUALIFIED"
    assert report["status"] == "COMPLETED_ONCE_PENDING_INDEPENDENT_RESULT_REVIEW"
    assert report["selected_next_target"] == execution.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == "INDEPENDENT_EXECUTION_RESULT_REVIEW_ONLY"
    authority = report["authority"]
    assert authority["consumed_review_verdict"] == execution.AUTHORIZED_REVIEW_VERDICT
    assert authority["authorized_execution_count"] == 1
    assert authority["performed_execution_count"] == 1
    assert {
        row["relative_path"]: row["sha256"]
        for row in authority["frozen_review_artifacts"]
    } == execution.REVIEW_HASHES
    assert authority["runner_sha256"] == _sha256(Path(execution.__file__).resolve())


def test_release_and_canonical_result_are_byte_identical() -> None:
    assert REPORT_PATH.read_bytes() == execution.CANONICAL_RESULT_PATH.read_bytes()


def test_launch_custody_is_complete_and_zero_survivor() -> None:
    custody = _report()["execution_custody"]
    assert custody["launch_count"] == 1
    assert custody["authority_consumed_before_worker_authorized"] is True
    assert custody["worker_exit_code"] == 0
    assert custody["timeout_initiated_at_utc"] is None
    assert custody["child_termination_at_utc"] is not None
    assert custody["zero_surviving_processes"] is True
    assert custody["finalized"] is True
    assert custody["peak_job_memory_within_limit"] is True
    assert custody["peak_job_memory_bytes"] <= 2048 * 1024 * 1024
    assert custody["process_group_mechanism"] == (
        "WINDOWS_JOB_OBJECT_KILL_ON_CLOSE_AND_JOB_MEMORY_LIMIT"
    )
    assert custody["raw_launcher_log_sha256"] == _sha256(execution.RAW_LOG_PATH)
    assert len(custody["launch_identity_sha256"]) == 64


def test_all_six_atomic_stages_completed_within_budget() -> None:
    rows = _report()["stage_records"]
    assert len(rows) == 6
    assert [row["stage_id"] for row in rows] == list(execution.STAGE_CAPS_SECONDS)
    assert all(row["status"] == "COMPLETE" for row in rows)
    assert all(row["within_stage_budget"] is True for row in rows)
    assert all(
        row["duration_seconds"] <= execution.STAGE_CAPS_SECONDS[row["stage_id"]]
        for row in rows
    )


def test_derivation_gate_passed_independently() -> None:
    gate = _report()["scientific_payload"]["derivation_gate"]
    assert gate["status"] == "PASS"
    obligations = gate["obligations"]
    assert obligations["strict_nonoverlap_all_cases"] is True
    assert obligations["both_form_factors_present"] is True
    assert obligations["center_distance_exponential_present"] is True
    assert obligations["yukawa_amplitude_exact"] == "1/3"
    assert obligations["sphere_exchange_symmetry"] is True
    assert obligations["point_particle_limit_F_to_one"] is True
    assert obligations["energy_units"] == "kg*m^2*s^-2=J"


def test_stable_evaluator_and_all_overlap_probes_passed() -> None:
    gate = _report()["scientific_payload"]["stable_evaluator_gate"]
    assert gate["status"] == "PASS"
    assert len(gate["overlap_rows"]) == 6
    assert all(row["passed"] for row in gate["overlap_rows"])
    assert all(
        row["absolute_difference"] <= row["tolerance"] for row in gate["overlap_rows"]
    )
    assert len(gate["case_evaluator_rows"]) == 8
    assert all(row["finite_positive_scaled_factors"] for row in gate["case_evaluator_rows"])
    assert gate["x_1000_direct_hyperbolic_path_used"] is False
    assert gate["silent_underflow_or_overflow_observed"] is False


def test_radial_path_self_converged_at_all_eleven_x_values() -> None:
    gate = _report()["scientific_payload"]["radial_cross_check_gate"]
    assert gate["radial_self_convergence"] == "PASS"
    assert gate["unique_x_count"] == 11
    assert len(gate["convergence_rows"]) == 11
    assert all(row["passed"] for row in gate["convergence_rows"])
    assert all(
        float(row["absolute_80_to_120_difference"]) <= float(row["tolerance"])
        for row in gate["convergence_rows"]
    )


def test_all_eight_analytic_radial_case_comparisons_passed() -> None:
    gate = _report()["scientific_payload"]["radial_cross_check_gate"]
    assert gate["analytic_radial_agreement"] == "PASS"
    assert len(gate["case_rows"]) == 8
    assert all(row["passed"] for row in gate["case_rows"])
    assert all(float(row["absolute_difference_J"]) <= float(row["agreement_tolerance_J"])
               for row in gate["case_rows"])
    assert max(float(row["relative_difference"]) for row in gate["case_rows"]) < 1e-13
    assert {row["case_id"] for row in gate["case_rows"]} >= {
        "LEGACY_STAGE_A_00_LARGE_X",
        "LEGACY_STAGE_A_01_TRANSITION",
        "LEGACY_STAGE_A_02_LONG_RANGE",
        "EXTREME_X_1000_UNEQUAL",
    }


def test_all_eight_live_mutations_were_detected() -> None:
    gate = _report()["scientific_payload"]["mutation_gate"]
    assert gate["status"] == "PASS"
    assert gate["mutation_count"] == gate["detected_count"] == 8
    assert gate["same_live_evaluator_radial_reference_and_adjudicator"] is True
    assert all(row["detected"] for row in gate["rows"])
    assert {row["mutation_id"] for row in gate["rows"]} == {
        "INTERPRET_RADIUS_AS_DIAMETER",
        "USE_SURFACE_GAP_AS_CENTER_DISTANCE",
        "OMIT_FOUR_PI_OVER_THREE_MASS_FACTOR",
        "OMIT_A_Y_ONE_THIRD",
        "OMIT_SECOND_SPHERE_FORM_FACTOR",
        "FLIP_YUKAWA_EXPONENTIAL_SIGN",
        "FORCE_DIRECT_LARGE_X_SINH_COSH_PATH",
        "FORCE_DIRECT_SMALL_X_CANCELLATION_PATH",
    }


def test_raw_log_contains_exact_stage_order_and_single_outcome() -> None:
    text = execution.RAW_LOG_PATH.read_text(encoding="utf-8")
    assert text.count("STAGE_START") == 6
    assert text.count("STAGE_END") == 6
    assert text.count("SCIENTIFIC_OUTCOME ANALYTIC_SPHERE_ORACLE_QUALIFIED") == 1
    positions = [text.index(f"STAGE_START {stage}") for stage in execution.STAGE_CAPS_SECONDS]
    assert positions == sorted(positions)


def test_downstream_firewalls_remained_closed() -> None:
    scope = _report()["scope"]
    assert scope["analytic_oracle_qualification_execution_performed"] is True
    for key, value in scope.items():
        if key != "analytic_oracle_qualification_execution_performed":
            assert value is False, key


def test_human_execution_record_reports_result_custody_and_claim_ceiling() -> None:
    text = HUMAN_PATH.read_text(encoding="utf-8")
    for token in (
        "ANALYTIC_SPHERE_ORACLE_QUALIFIED",
        "1 / 1",
        "analytic derivation:       PASS",
        "radial self-convergence:   PASS",
        "EXTREME_X_1000_UNEQUAL",
        "8 / 8 DETECTED",
        "23,298,048 bytes",
        execution.SELECTED_NEXT_TARGET,
        "UNADJUDICATED",
    ):
        assert token in text
