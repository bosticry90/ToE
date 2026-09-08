from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
PREFIX = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v1"
)
RESULT = ROOT / f"{PREFIX}.json"
SIDECAR = ROOT / f"{PREFIX}.json.sha256"
MARKER = ROOT / f"{PREFIX}.authority_consumed.json"
STAGES = ROOT / f"{PREFIX}.stages.json"
LOG = ROOT / f"{PREFIX}.log"
SOURCE = ROOT / (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v1.py"
)
RESULT_SHA256 = "3a6bc5738f774668c3d1387d7557d0c0654bb0db2a875f0237b655f539dec4ee"
SOURCE_SHA256 = "ebadb20d9a256af4251e488c0fc010e30cd90510de7b373191147f085fed1eca"


def _load(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_one_shot_authority_and_source_custody_are_exact() -> None:
    result = _load(RESULT)
    marker = _load(MARKER)
    assert _sha(RESULT) == RESULT_SHA256
    assert _sha(SOURCE) == SOURCE_SHA256
    assert SIDECAR.read_text(encoding="ascii").strip() == (
        f"{RESULT_SHA256}  {PREFIX}.json"
    )
    assert marker["authority"] == (
        "execute_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v1_once"
    )
    assert marker["source_sha256"] == SOURCE_SHA256
    assert marker["run_id"] == result["run_id"]
    assert marker["status"] == "CONSUMED_BY_SINGLE_LAUNCH_NO_RERUN"
    assert result["execution_count"] == 1


def test_complete_preserved_negative_outcome_is_exact() -> None:
    result = _load(RESULT)
    assert result["terminal_outcome"] == (
        "EXPLORATORY_IMPLEMENTATION_COMPLETED_WITH_RECORDED_FAILURES"
    )
    assert result["completeness"]["all_required_records_complete"] is True
    assert result["implementation"]["status"] == "COMPLETE"
    assert result["implementation"]["production_import_or_dispatch"] is False
    assert result["implementation"]["historical_cubature_called"] is False
    assert result["administrative"]["automatic_retry_or_rerun"] is False
    assert result["administrative"]["downstream_scientific_execution"] is False


def test_corrected_real_aggregate_serialization_control_passed() -> None:
    controls = {
        row["control_id"]: row for row in _load(RESULT)["infrastructure"]["control_rows"]
    }
    c12 = controls["C12_CANONICAL_ROUND_TRIP_BYTES_AND_SHA256_STABLE"]
    assert c12["passed"] is True
    assert c12["schema_complete_final_aggregate"] is True
    assert c12["actual_nested_adjudication_record_exercised"] is True
    assert c12["decimal_count_before_normalization"] == 2
    assert c12["decimal_count_after_normalization"] == 0
    assert c12["strict_schema_validation_passed"] is True
    assert c12["atomic_write_and_postwrite_verification_passed"] is True
    assert c12["bytes_identical"] is True


def test_all_eight_stages_and_required_record_counts_completed() -> None:
    result = _load(RESULT)
    stages = _load(STAGES)["stages"]
    assert len(stages) == 8
    assert stages == result["stages"]
    assert all(row["status"] == "COMPLETE" for row in stages)
    assert result["infrastructure"]["control_count_completed"] == 12
    assert result["regressions"]["case_count_completed"] == 8
    assert result["boundary_and_limits"]["probe_count_completed"] == 13
    assert result["mutations"]["mutation_count_completed"] == 12
    assert result["runtime"]["trial_count"] == 5


def test_preserved_passing_sections_do_not_override_mandatory_failures() -> None:
    result = _load(RESULT)
    assert result["interface"]["passed"] is True
    assert result["regressions"]["passed"] is True
    assert all(row["passed"] for row in result["regressions"]["rows"])
    assert result["boundary_and_limits"]["passed"] is True
    assert result["runtime"]["passed"] is True
    assert result["infrastructure"]["passed"] is False
    assert result["mutations"]["passed"] is False


def _bad_descriptor_child(row: dict[str, object]) -> bool:
    return (
        row["passed"] is False
        and row["returncode"] == 1
        and "Bad file descriptor" in row["stdout_ascii"]
        and "builtins.OSError" in row["stdout_ascii"]
    )


def test_all_twenty_child_routes_record_the_same_pre_fixture_plumbing_failure() -> None:
    result = _load(RESULT)
    synthetic_rows = result["infrastructure"]["mutation_route_rows"]
    kernel_rows = result["mutations"]["rows"]
    assert len(synthetic_rows) == 8
    assert len(kernel_rows) == 12
    assert all(_bad_descriptor_child(row) for row in synthetic_rows)
    assert all(_bad_descriptor_child(row) for row in kernel_rows)
    controls = {
        row["control_id"]: row for row in result["infrastructure"]["control_rows"]
    }
    assert controls["C08_ALL_EIGHT_MUTATION_ROUTES_DETECT"]["passed"] is False


def test_result_artifact_set_is_preserved_and_nonempty() -> None:
    for path in (RESULT, SIDECAR, MARKER, STAGES, LOG):
        assert path.is_file()
        assert path.stat().st_size > 0
