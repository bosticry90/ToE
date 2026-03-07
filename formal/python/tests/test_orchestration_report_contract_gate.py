from __future__ import annotations

import json
from pathlib import Path

from formal.python.orchestration.runner import DEFAULT_MANIFEST_REL
from formal.python.orchestration.runner import DEFAULT_REPORT_REL


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = _find_repo_root(Path(__file__))
CONTRACT_PATH = REPO_ROOT / "formal/docs/release/TOE_ORCHESTRATION_REPORT_CONTRACT_v0.md"
SCHEMA_PATH = REPO_ROOT / "formal/docs/release/TOE_ADJUDICATION_REPORT_SCHEMA_v0.json"


def test_orchestration_report_contract_paths_are_pinned() -> None:
    text = CONTRACT_PATH.read_text(encoding="utf-8")
    assert str(DEFAULT_MANIFEST_REL).replace("\\", "/") in text
    assert str(DEFAULT_REPORT_REL).replace("\\", "/") in text
    assert "formal/docs/release/TOE_ADJUDICATION_REPORT_SCHEMA_v0.json" in text
    assert "formal/python/tests/test_orchestration_report_contract_gate.py" in text


def test_orchestration_report_schema_required_fields_are_present() -> None:
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    required = set(schema.get("required", []))
    expected = {
        "schema_id",
        "generated_at_utc",
        "runner_version",
        "checks_run",
        "failures",
        "uncertainties",
        "speculative_flags",
        "manual_review_required",
    }
    assert expected.issubset(required)
