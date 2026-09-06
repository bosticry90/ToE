from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RESULT = ROOT / "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_20260719_v0.json"
MARKER = ROOT / "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_20260719_v0.authority_consumed.json"
STAGES = ROOT / "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_20260719_v0.stages.json"
LOG = ROOT / "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_20260719_v0.log"


def _load(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_one_shot_authority_is_consumed_once() -> None:
    result = _load(RESULT)
    marker = _load(MARKER)
    assert result["authority_consumed"] is True
    assert result["execution_count"] == 1
    assert marker["status"] == "CONSUMED_BY_SINGLE_LAUNCH_NO_RERUN"
    assert marker["run_id"] == result["run_id"]


def test_serialization_failure_is_the_exclusive_terminal_outcome() -> None:
    result = _load(RESULT)
    assert result["terminal_outcome"] == "EXPLORATORY_IMPLEMENTATION_RESULT_SERIALIZATION_FAILED_INCOMPLETE"
    assert result["administrative"]["failure_type"] == "builtins.TypeError"
    assert result["administrative"]["launcher_exit_code"] == 1
    assert result["completeness"]["all_required_decision_records_serialized"] is False
    assert result["completeness"]["scientific_or_qualification_classification_suppressed"] is True


def test_all_eight_stage_boundaries_are_preserved_but_not_overinterpreted() -> None:
    result = _load(RESULT)
    stages = _load(STAGES)["stages"]
    assert len(stages) == 8
    assert all(row["status"] == "COMPLETE" for row in stages)
    assert result["stage_custody"] == stages
    for section in (
        "analytic_regression_performance",
        "derivative_reference_performance",
        "boundary_and_limit_behavior",
    ):
        assert result["sections"][section]["scientific_pass_or_fail"] == "NOT_ADJUDICATED"


def test_custody_hashes_reproduce() -> None:
    custody = _load(RESULT)["preserved_custody"]
    assert custody["authority_consumption_sha256"] == _sha(MARKER)
    assert custody["stage_checkpoint_sha256"] == _sha(STAGES)
    assert custody["raw_log_sha256"] == _sha(LOG)


def test_required_exploratory_labels_and_firewalls_remain_exact() -> None:
    result = _load(RESULT)
    assert result["result_labels"] == [
        "EXPLORATORY_IMPLEMENTATION_RESULT",
        "NON_PRODUCTION",
        "NON_ADJUDICATIVE",
        "NO_SCIENTIFIC_CLAIM",
    ]
    assert result["implementation"]["production_code_or_dispatch_changed"] is False
    assert "No kernel qualification" in result["claim_ceiling"]
    assert result["next_authority"] == (
        "review_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v0_execution_result"
    )
