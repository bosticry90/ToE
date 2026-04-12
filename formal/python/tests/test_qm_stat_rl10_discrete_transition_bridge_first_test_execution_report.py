from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_first_test_execution_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_first_test_packet_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_test_packet_20260412_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
            },
            "execution_payload": {
                "test_observable_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "signal_threshold": 0.05,
                "observed_signal_strength": 0.12,
                "falsification_observed": False,
                "undeclared_structure_needed": [],
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "BRIDGE_SEAM_SIGNAL_PRODUCED",
                    "BRIDGE_SEAM_INTERNAL_ONLY",
                    "BRIDGE_SEAM_PATH_FALSIFIED",
                    "BRIDGE_SEAM_REQUIRES_FURTHER_DECLARED_STRUCTURE",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_TERMINAL_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_SEAM_FIRST_TEST_EXECUTION_ONLY",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_packet_20260412_v0.json",
        {
            "criteria": {
                "bridge_observable_ready": True,
                "transition_structure_coherent": True,
                "governance_boundary_preserved": True,
            },
            "summary": {"terminal_outcome": "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE"},
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "baseline_id": "OV-RL-10",
            }
        },
    )


def test_execution_reports_signal_produced_when_threshold_is_met(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SEAM_SIGNAL_PRODUCED"


def test_execution_reports_internal_only_when_signal_is_below_threshold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["execution_payload"]["observed_signal_strength"] = 0.01
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SEAM_INTERNAL_ONLY"


def test_execution_reports_path_falsified_when_flagged(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["execution_payload"]["falsification_observed"] = True
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SEAM_PATH_FALSIFIED"


def test_execution_reports_requires_structure_when_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["execution_payload"]["undeclared_structure_needed"] = ["EXTRA_BRIDGE_OPERATOR"]
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["terminal_outcome"]
        == "BRIDGE_SEAM_REQUIRES_FURTHER_DECLARED_STRUCTURE"
    )