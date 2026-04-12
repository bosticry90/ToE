from __future__ import annotations

import json
from pathlib import Path
import shutil
import uuid

from formal.python.tools.dual_track_cutover_report_generate import REPO_ROOT, build_report


def _write_runtime_artifact(
    path: Path,
    *,
    measurement_mode: str,
    governance_suite: float,
    checkpoint_ladder: float,
) -> None:
    payload = {
        "schema_id": "RUNTIME_ARTIFACT_TEST_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "measurement_mode": measurement_mode,
        "runtime_seconds": {
            "governance_suite": governance_suite,
            "checkpoint_ladder": checkpoint_ladder,
            "branch_health_full_pytest": 100.0,
        },
    }
    path.write_text(json.dumps(payload), encoding="utf-8")


def _repo_scoped_temp_paths() -> tuple[Path, Path, Path]:
    base = REPO_ROOT / "formal" / "output" / "reports" / "_pytest_dual_track_cutover" / uuid.uuid4().hex
    base.mkdir(parents=True, exist_ok=True)
    return base, base / "baseline.json", base / "current.json"


def test_cutover_pass_requires_measured_modes_even_with_threshold_improvement() -> None:
    base, baseline, current = _repo_scoped_temp_paths()

    try:
        _write_runtime_artifact(
            baseline,
            measurement_mode="MANUAL",
            governance_suite=100.0,
            checkpoint_ladder=100.0,
        )
        _write_runtime_artifact(
            current,
            measurement_mode="MANUAL",
            governance_suite=80.0,
            checkpoint_ladder=80.0,
        )

        report = build_report(
            baseline_path=baseline,
            current_path=current,
            governance_required_improvement=10.0,
            checkpoint_required_improvement=10.0,
            captured_at_utc=None,
        )

        assert report["metrics"]["governance_suite"]["threshold_pass"] is True
        assert report["metrics"]["checkpoint_ladder"]["threshold_pass"] is True
        assert report["measurement_policy"]["measured_mode_satisfied"] is False
        assert report["cutover_readiness"]["overall_pass"] is False
    finally:
        shutil.rmtree(base, ignore_errors=True)


def test_cutover_pass_succeeds_when_thresholds_and_measured_modes_satisfied() -> None:
    base, baseline, current = _repo_scoped_temp_paths()

    try:
        _write_runtime_artifact(
            baseline,
            measurement_mode="MEASURED",
            governance_suite=100.0,
            checkpoint_ladder=100.0,
        )
        _write_runtime_artifact(
            current,
            measurement_mode="MEASURED",
            governance_suite=80.0,
            checkpoint_ladder=80.0,
        )

        report = build_report(
            baseline_path=baseline,
            current_path=current,
            governance_required_improvement=10.0,
            checkpoint_required_improvement=10.0,
            captured_at_utc=None,
        )

        assert report["measurement_policy"]["measured_mode_satisfied"] is True
        assert report["cutover_readiness"]["overall_pass"] is True
    finally:
        shutil.rmtree(base, ignore_errors=True)
