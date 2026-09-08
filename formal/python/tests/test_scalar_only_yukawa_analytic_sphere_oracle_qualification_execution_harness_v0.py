from __future__ import annotations

import inspect

from formal.python.tools import (
    scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_v0 as execution,
)


def test_harness_consumes_exact_review_authority_without_running_science() -> None:
    preflight = execution.static_preflight(require_unused_authority=False)
    assert preflight["target"] == execution.TARGET
    assert preflight["review_verdict"] == execution.AUTHORIZED_REVIEW_VERDICT
    assert preflight["case_count"] == 8
    assert preflight["total_timeout_seconds"] == 600
    assert preflight["memory_limit_mib"] == 2048


def test_stage_caps_are_exact_and_sum_to_total() -> None:
    assert execution.STAGE_CAPS_SECONDS == {
        "O1_PREFLIGHT_AND_CUSTODY": 20,
        "O2_DERIVATION_DOMAIN_AND_DIMENSIONS": 60,
        "O3_STABLE_EVALUATOR_AND_OVERLAPS": 90,
        "O4_INDEPENDENT_RADIAL_CROSS_CHECK": 300,
        "O5_MUTATIONS_AND_ADJUDICATION": 90,
        "O6_ATOMIC_FINALIZATION": 40,
    }
    assert sum(execution.STAGE_CAPS_SECONDS.values()) == execution.TOTAL_TIMEOUT_SECONDS


def test_launcher_uses_start_gate_new_process_group_and_windows_job_object() -> None:
    source = inspect.getsource(execution)
    for token in (
        "CREATE_NEW_PROCESS_GROUP",
        "WINDOWS_JOB_OBJECT_KILL_ON_CLOSE_AND_JOB_MEMORY_LIMIT",
        "AssignProcessToJobObject",
        "JOB_OBJECT",
        "START_GATE_PATH.write_text",
        "authority_consumed_before_worker_authorized",
        "zero_surviving_processes",
    ):
        assert token in source


def test_worker_orders_derivation_before_evaluator_radial_and_mutations() -> None:
    source = inspect.getsource(execution._worker)
    offsets = [
        source.index("_derivation_gate"),
        source.index("_evaluator_gate"),
        source.index("_radial_gate"),
        source.index("_mutation_gate"),
    ]
    assert offsets == sorted(offsets)
    assert "SPHERE_ORACLE_NOT_VALID_OVER_REQUIRED_DOMAIN" in source
    assert "ANALYTIC_FORMULA_DERIVED_BUT_NUMERICAL_EVALUATOR_UNSTABLE" in source
    assert "ANALYTIC_ORACLE_CROSS_CHECK_FAILED" in source
    assert "ANALYTIC_SPHERE_ORACLE_QUALIFIED" in source


def test_radial_path_is_one_dimensional_scaled_and_closed_form_free() -> None:
    source = inspect.getsource(execution._radial_h)
    assert "mp.expm1" in source
    assert "mp.quad" in source
    assert 'method="tanh-sinh"' in source
    assert "_h_stable" not in source
    assert "cosh" not in source
    assert "mp.sinh(" not in source


def test_mutations_route_against_live_radial_reference() -> None:
    source = inspect.getsource(execution._mutation_gate)
    for mutation in (
        "INTERPRET_RADIUS_AS_DIAMETER",
        "USE_SURFACE_GAP_AS_CENTER_DISTANCE",
        "OMIT_FOUR_PI_OVER_THREE_MASS_FACTOR",
        "OMIT_A_Y_ONE_THIRD",
        "OMIT_SECOND_SPHERE_FORM_FACTOR",
        "FLIP_YUKAWA_EXPONENTIAL_SIGN",
        "FORCE_DIRECT_LARGE_X_SINH_COSH_PATH",
        "FORCE_DIRECT_SMALL_X_CANCELLATION_PATH",
    ):
        assert mutation in source
    assert "yukawa_radial_reference_J" in source


def test_harness_never_calls_production_cubature_or_downstream_paths() -> None:
    source = inspect.getsource(execution)
    assert "four_dimensional" not in source
    assert "gauss_legendre" not in source
    assert "jacobian" not in source.lower().replace('"jacobian_or_svd_computed"', "")
    assert "eta_lambda" not in source
