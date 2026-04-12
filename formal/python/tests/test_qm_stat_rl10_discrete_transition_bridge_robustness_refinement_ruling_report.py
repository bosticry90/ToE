from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_robustness_refinement_ruling_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_robustness_refinement_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_20260412_v0.json"
            },
            "ruling_contract": {
                "allowed_outcomes": [
                    "BRIDGE_SIGNAL_PROBE_READY",
                    "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD",
                    "BRIDGE_SIGNAL_PATH_FALSIFIED",
                    "ROBUSTNESS_REFINEMENT_INCONCLUSIVE",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_REFINEMENT_RULING_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_ROBUSTNESS_REFINEMENT_RULING_ONLY",
                "default_outcome": "ROBUSTNESS_REFINEMENT_INCONCLUSIVE",
            },
        },
    )


def test_refinement_ruling_confirms_allowed_outcome(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_REFINEMENT_RULING_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "BRIDGE_SIGNAL_PROBE_READY"}},
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["ruling_status"] == "TERMINAL_OUTCOME_CONFIRMED"
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_PROBE_READY"


def test_refinement_ruling_blocks_invalid_to_default(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_REFINEMENT_RULING_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "INVALID"}},
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["ruling_status"] == "TERMINAL_OUTCOME_BLOCKED"
    assert report["summary"]["terminal_outcome"] == "ROBUSTNESS_REFINEMENT_INCONCLUSIVE"
