from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_ruling_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_external_comparator_binding_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_20260412_v0.json"
            },
            "ruling_contract": {
                "allowed_outcomes": [
                    "EXTERNAL_COMPARATOR_BINDING_CONFIRMED",
                    "BRIDGE_SIGNAL_PROBE_READY",
                    "COMPARATOR_BINDING_PARTIAL_HOLD",
                    "BRIDGE_SIGNAL_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_BINDING_RULING_OUTCOME",
                "no_loop_rule": "ONE_EXTERNAL_COMPARATOR_BINDING_RULING_ONLY",
                "default_outcome": "COMPARATOR_BINDING_PARTIAL_HOLD",
            },
        },
    )


def test_binding_ruling_confirms_allowed_outcome(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARATOR_BINDING_RULING_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "EXTERNAL_COMPARATOR_BINDING_CONFIRMED"}},
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["ruling_status"] == "TERMINAL_OUTCOME_CONFIRMED"
    assert report["summary"]["terminal_outcome"] == "EXTERNAL_COMPARATOR_BINDING_CONFIRMED"


def test_binding_ruling_blocks_invalid_outcome_to_default(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARATOR_BINDING_RULING_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "INVALID"}},
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["ruling_status"] == "TERMINAL_OUTCOME_BLOCKED"
    assert report["summary"]["terminal_outcome"] == "COMPARATOR_BINDING_PARTIAL_HOLD"