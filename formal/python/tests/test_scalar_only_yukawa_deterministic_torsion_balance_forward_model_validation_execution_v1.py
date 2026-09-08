from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1
    as execution,
)


ROOT = find_repo_root(Path(__file__))
RESULT_PATH = ROOT / execution.REPORT_RELATIVE_PATH
OUTPUT_ROOT = ROOT / execution.OUTPUT_RELATIVE_DIRECTORY
ADDENDUM_PATH = ROOT / (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_"
    "FORWARD_MODEL_VALIDATION_EXECUTION_CUSTODY_ADDENDUM_20260719_v1.json"
)


def _json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _rows(name: str) -> list[dict[str, str]]:
    with (OUTPUT_ROOT / name).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_execution_result_copies_and_manifest_are_exact() -> None:
    result = _json(RESULT_PATH)
    assert RESULT_PATH.read_bytes() == (OUTPUT_ROOT / "execution_result.json").read_bytes()
    assert result["artifact_manifest"]["artifact_count"] == 10
    for row in result["artifact_manifest"]["rows"]:
        path = ROOT / row["relative_path"]
        assert path.stat().st_size == row["byte_count"]
        assert _sha256(path) == row["sha256"]
    assert execution.check_execution() == 0


def test_single_authority_is_consumed_and_second_execution_fails_closed() -> None:
    result = _json(RESULT_PATH)
    assert result["authority"]["authorized_execution_count"] == 1
    assert result["authority"]["consumed_execution_count"] == 1
    assert result["scope"]["single_execution_authority_consumed"] is True
    with pytest.raises(RuntimeError, match="already consumed"):
        execution.execute_once()


def test_early_physical_control_block_is_exact() -> None:
    result = _json(RESULT_PATH)
    summary = result["execution_summary"]
    assert result["outcome"] == "BLOCKED_PRODUCTION_KERNEL_VALIDATION"
    assert summary["pre_identifiability_controls_pass"] is False
    assert result["secondary_outcome"] == (
        "NO_IDENTIFIABILITY_CALCULATION_DUE_TO_EARLY_PHYSICAL_CONTROL_FAILURE"
    )
    detail = summary["detail"]["pre_identifiability"]
    assert detail == {
        "benchmark_count": 4,
        "benchmark_pass_count": 3,
        "convergence_control_count": 6,
        "convergence_pass_count": 4,
        "mutation_count": 5,
        "mutation_pass_count": 5,
        "symmetry_control_count": 6,
        "symmetry_pass_count": 6,
    }


def test_exact_benchmark_and_convergence_failures_are_preserved() -> None:
    benchmark_failures = [row for row in _rows("benchmarks.csv") if row["pass"] == "FAIL"]
    assert {(row["benchmark_id"], row["metric_id"]) for row in benchmark_failures} == {
        ("UNIFORM_SPHERE_FORM_FACTOR", "max_production_vs_order24_relative_error"),
        ("UNIFORM_SPHERE_FORM_FACTOR", "max_order16_vs_order24_relative_error"),
    }
    assert [row["control_id"] for row in _rows("convergence.csv") if row["pass"] == "FAIL"] == [
        "ANGULAR_DFT_256_VS_512",
        "DENSITY_CUBATURE_16_VS_24",
    ]
    assert float(benchmark_failures[0]["value"]) == pytest.approx(6.867902041407599e-2)
    assert float(benchmark_failures[1]["value"]) == pytest.approx(4.202776018628042e-1)


def test_mutation_and_symmetry_controls_all_pass() -> None:
    mutations = _rows("mutations.csv")
    symmetry = _rows("symmetry_controls.csv")
    assert len(mutations) == 5 and all(row["pass"] == "PASS" for row in mutations)
    assert len(symmetry) == 6 and all(row["pass"] == "PASS" for row in symmetry)


def test_identifiability_and_stage_b_were_not_reached() -> None:
    result = _json(RESULT_PATH)
    assert result["execution_summary"]["detail"]["identifiability"] == {
        "status": "NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK"
    }
    scope = result["scope"]
    for key in (
        "jacobian_computed",
        "singular_values_computed",
        "eta_lambda_computed",
        "physical_identifiability_evaluated",
        "stage_b_eligible_for_fresh_selection",
        "stage_b_authorized",
        "monte_carlo_executed",
        "sensitivity_forecast_produced",
        "numerical_alpha_bound_computed",
    ):
        assert scope[key] is False
    assert _rows("jacobian_columns.csv") == [
        {"status": "NOT_COMPUTED_EARLY_PHYSICAL_CONTROL_BLOCK"}
    ]


def test_internal_repeat_and_next_review_authority_are_exact() -> None:
    result = _json(RESULT_PATH)
    assert result["canonical_repeat"] == {
        "artifact_count_compared": 10,
        "byte_identical": True,
        "internal_run_count": 2,
    }
    assert result["selected_next_target"] == execution.SELECTED_NEXT_TARGET
    assert result["current_posture"]["automatic_v2"] == "NOT_AUTHORIZED"
    assert result["current_posture"]["stage_b"] == "NOT_AUTHORIZED"


def test_runtime_sources_and_launch_recovery_are_hash_pinned() -> None:
    assert _sha256(
        ROOT / "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py"
    ) == "4995c467f766466583c53c7904e2f1bb35b7c02970aece4a20e2315403ed8cac"
    assert _sha256(
        ROOT
        / "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1.py"
    ) == "ec0209a433027d8e8523d9e0f21ba3662ccec559de33ea042cb0a765b64571ae"
    addendum = _json(ADDENDUM_PATH)
    assert addendum["launch_attempt_count"] == 3
    assert addendum["production_compute_pass_count_across_all_attempts"] == 3
    assert addendum["completed_canonical_execution_count"] == 1
    assert addendum["single_execution_authority_consumed"] is True
    assert addendum["recovery_change"]["changed_scientific_parameter_or_threshold"] is False
    assert addendum["recovery_change"]["changed_production_kernel_or_geometry"] is False
