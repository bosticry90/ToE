from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_first_test_ruling_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_first_test_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json"
            },
            "ruling_contract": {
                "allowed_outcomes": [
                    "BRIDGE_SEAM_SIGNAL_PRODUCED",
                    "BRIDGE_SEAM_INTERNAL_ONLY",
                    "BRIDGE_SEAM_PATH_FALSIFIED",
                    "BRIDGE_SEAM_REQUIRES_FURTHER_DECLARED_STRUCTURE",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_TERMINAL_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_SEAM_FIRST_TEST_RULING_ONLY",
                "default_ruling": "BRIDGE_SEAM_INTERNAL_ONLY",
            },
        },
    )


def test_ruling_confirms_allowed_execution_terminal_outcome(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_RULING_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "BRIDGE_SEAM_SIGNAL_PRODUCED"}},
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["ruling_status"] == "TERMINAL_OUTCOME_CONFIRMED"
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SEAM_SIGNAL_PRODUCED"


def test_ruling_uses_default_when_execution_outcome_is_invalid(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_RULING_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "INVALID_OUTCOME"}},
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["ruling_status"] == "TERMINAL_OUTCOME_BLOCKED"
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SEAM_INTERNAL_ONLY"