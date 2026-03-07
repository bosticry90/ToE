from __future__ import annotations

import json
import asyncio
import sys
from pathlib import Path

from formal.python.orchestration.runner import CheckSpec
from formal.python.orchestration.runner import SCHEMA_ID
from formal.python.orchestration.runner import _load_manifest
from formal.python.orchestration.runner import run_checks


def test_load_manifest_expands_python_token(tmp_path: Path) -> None:
    manifest = {
        "schema_id": "TOE_ASYNC_ORCHESTRATION_MANIFEST_v0",
        "checks": [
            {
                "check_id": "smoke",
                "command": ["{python}", "-c", "print('ok')"],
                "timeout_seconds": 10,
            }
        ],
    }
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

    checks = _load_manifest(manifest_path)
    assert len(checks) == 1
    assert checks[0].command[0] == sys.executable


def test_run_checks_emits_required_report_fields() -> None:
    checks = [
        CheckSpec(
            check_id="pass_case",
            command=[sys.executable, "-c", "print('ok')"],
            timeout_seconds=30,
        ),
        CheckSpec(
            check_id="fail_case",
            command=[sys.executable, "-c", "import sys; sys.exit(3)"],
            timeout_seconds=30,
        ),
    ]

    report = asyncio.run(run_checks(checks, max_concurrency=2))

    assert report["schema_id"] == SCHEMA_ID
    assert isinstance(report["checks_run"], list)
    assert isinstance(report["failures"], list)
    assert isinstance(report["uncertainties"], list)
    assert isinstance(report["speculative_flags"], list)
    assert isinstance(report["manual_review_required"], list)
    assert "fail_case" in report["failures"]

    by_id = {row["check_id"]: row for row in report["checks_run"]}
    assert by_id["pass_case"]["status"] == "passed"
    assert by_id["fail_case"]["status"] == "failed"
