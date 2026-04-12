from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_external_comparability_adjudication_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_external_comparability_adjudication_20260412_v0.json",
                "bridge_first_test_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
            },
            "binding_spec": {
                "external_comparator_id": "OV-RL-10",
                "external_comparator_schema": "OV-RL-10_entropy_balance_comparator/v0",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "binding_success_margin_min": 0.06,
                "probe_ready_margin_min": 0.10,
                "partial_hold_margin_min": 0.03,
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "EXTERNAL_COMPARATOR_BINDING_CONFIRMED",
                    "BRIDGE_SIGNAL_PROBE_READY",
                    "COMPARATOR_BINDING_PARTIAL_HOLD",
                    "BRIDGE_SIGNAL_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_BINDING_EXECUTION_OUTCOME",
                "no_loop_rule": "ONE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_PACKET_ONLY",
            },
        },
    )


def _seed_common(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparability_adjudication_20260412_v0.json",
        {"summary": {"adjudication_outcome": "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CONFIRMED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "baseline_id": "OV-RL-10",
                "baseline_schema": "OV-RL-10_entropy_balance_comparator/v0",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SEAM_SIGNAL_PRODUCED",
                "test_observable_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "signal_threshold": 0.05,
                "observed_signal_strength": 0.12,
            }
        },
    )


def test_binding_execution_reports_confirmed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EXTERNAL_COMPARATOR_BINDING_CONFIRMED"


def test_binding_execution_reports_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_external_comparability_adjudication_20260412_v0.json",
        {"summary": {"adjudication_outcome": "BRIDGE_SIGNAL_PROBE_READY"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SEAM_SIGNAL_PRODUCED",
                "test_observable_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "signal_threshold": 0.05,
                "observed_signal_strength": 0.16,
            }
        },
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_PROBE_READY"


def test_binding_execution_reports_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SEAM_SIGNAL_PRODUCED",
                "test_observable_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "signal_threshold": 0.05,
                "observed_signal_strength": 0.08,
            }
        },
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "COMPARATOR_BINDING_PARTIAL_HOLD"


def test_binding_execution_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SEAM_PATH_FALSIFIED",
                "test_observable_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "signal_threshold": 0.05,
                "observed_signal_strength": 0.01,
            }
        },
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "BRIDGE_SIGNAL_PATH_FALSIFIED"