from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_execution_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_external_comparator_binding_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_20260412_v0.json",
                "bridge_external_comparator_binding_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_ruling_20260412_v0.json",
            },
            "robustness_spec": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "baseline_signal_margin": 0.07,
                "perturbation_delta": 0.03,
                "probe_ready_margin_min": 0.06,
                "hold_margin_min": 0.02,
                "path_falsification_observed": False,
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "BRIDGE_SIGNAL_PROBE_READY",
                    "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD",
                    "BRIDGE_SIGNAL_ROBUSTNESS_FAILURE",
                    "BRIDGE_SIGNAL_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_ROBUSTNESS_EXECUTION_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_PROBE_READINESS_ROBUSTNESS_EXECUTION_ONLY",
            },
        },
    )


def _seed_common(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "EXTERNAL_COMPARATOR_BINDING_CONFIRMED",
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_ruling_20260412_v0.json",
        {
            "summary": {
                "ruling_status": "TERMINAL_OUTCOME_CONFIRMED",
                "terminal_outcome": "EXTERNAL_COMPARATOR_BINDING_CONFIRMED",
            }
        },
    )


def test_robustness_execution_reports_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_READINESS_ROBUSTNESS_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["robustness_spec"]["perturbation_delta"] = 0.00
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_PROBE_READY"


def test_robustness_execution_reports_bound_but_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_READINESS_ROBUSTNESS_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD"


def test_robustness_execution_reports_failure(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_READINESS_ROBUSTNESS_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["robustness_spec"]["perturbation_delta"] = 0.08
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_ROBUSTNESS_FAILURE"


def test_robustness_execution_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_READINESS_ROBUSTNESS_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["robustness_spec"]["path_falsification_observed"] = True
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_PATH_FALSIFIED"