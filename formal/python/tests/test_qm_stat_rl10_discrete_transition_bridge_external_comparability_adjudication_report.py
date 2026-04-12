from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_external_comparability_adjudication_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_signal_interpretation_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json",
                "bridge_first_test_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
                "bridge_first_test_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_test_ruling_20260412_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
            },
            "comparator_binding": {
                "external_comparator_id": "OV-RL-10",
                "external_comparator_schema": "OV-RL-10_entropy_balance_comparator/v0",
                "comparable_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
                "confirmation_signal_margin_min": 0.05,
                "probe_ready_signal_margin_min": 0.10,
            },
            "adjudication_contract": {
                "allowed_outcomes": [
                    "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CONFIRMED",
                    "BRIDGE_SIGNAL_PROBE_READY",
                    "BRIDGE_SIGNAL_CANDIDATE_ONLY_HOLD",
                    "BRIDGE_SIGNAL_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_ADJUDICATION_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_EXTERNAL_COMPARABILITY_ADJUDICATION_ONLY",
                "default_outcome": "BRIDGE_SIGNAL_CANDIDATE_ONLY_HOLD",
            },
        },
    )


def _seed_common_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json",
        {"summary": {"interpretation_outcome": "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE"}},
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
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_ruling_20260412_v0.json",
        {
            "summary": {
                "ruling_status": "TERMINAL_OUTCOME_CONFIRMED",
                "terminal_outcome": "BRIDGE_SEAM_SIGNAL_PRODUCED",
            }
        },
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


def test_adjudication_reports_externally_comparable_confirmed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARABILITY_ADJUDICATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["adjudication_outcome"] == "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CONFIRMED"


def test_adjudication_reports_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARABILITY_ADJUDICATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json",
        {"summary": {"interpretation_outcome": "BRIDGE_SIGNAL_PROBE_READY"}},
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
    assert report["summary"]["adjudication_outcome"] == "BRIDGE_SIGNAL_PROBE_READY"


def test_adjudication_reports_candidate_only_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARABILITY_ADJUDICATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)
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
    assert report["summary"]["adjudication_outcome"] == "BRIDGE_SIGNAL_CANDIDATE_ONLY_HOLD"


def test_adjudication_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARABILITY_ADJUDICATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)
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
    assert report["summary"]["adjudication_outcome"] == "BRIDGE_SIGNAL_PATH_FALSIFIED"