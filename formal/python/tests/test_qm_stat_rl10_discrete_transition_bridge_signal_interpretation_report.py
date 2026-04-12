from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_signal_interpretation_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_first_test_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
                "bridge_first_test_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_test_ruling_20260412_v0.json",
                "bridge_first_test_packet_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_test_packet_20260412_v0.json",
            },
            "adjudication_policy": {
                "allowed_outcomes": [
                    "BRIDGE_SIGNAL_INTERNAL_ONLY",
                    "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE",
                    "BRIDGE_SIGNAL_PROBE_READY",
                    "BRIDGE_SIGNAL_INSUFFICIENT_HOLD",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_INTERPRETATION_OUTCOME",
                "probe_ready_signal_margin": 0.10,
                "externally_comparable_signal_margin": 0.00,
                "insufficient_hold_signal_margin": -0.02,
                "noise_floor_max": 0.03,
                "default_outcome": "BRIDGE_SIGNAL_INTERNAL_ONLY",
                "no_loop_rule": "ONE_BRIDGE_SIGNAL_INTERPRETATION_ONLY",
            },
        },
    )


def _seed_inputs(root: Path, *, signal_threshold: float, signal_strength: float) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_packet_20260412_v0.json",
        {
            "criteria": {"bridge_observable_ready": True},
            "summary": {"terminal_outcome": "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE"},
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SEAM_SIGNAL_PRODUCED",
                "signal_threshold": signal_threshold,
                "observed_signal_strength": signal_strength,
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


def test_interpretation_reports_probe_ready_for_strong_signal(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_INTERPRETATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, signal_threshold=0.05, signal_strength=0.20)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["interpretation_outcome"] == "BRIDGE_SIGNAL_PROBE_READY"


def test_interpretation_reports_externally_comparable_candidate_for_moderate_signal(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_INTERPRETATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, signal_threshold=0.05, signal_strength=0.12)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["interpretation_outcome"]
        == "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE"
    )


def test_interpretation_reports_internal_only_if_signal_not_produced(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_INTERPRETATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, signal_threshold=0.05, signal_strength=0.12)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "BRIDGE_SEAM_INTERNAL_ONLY",
                "signal_threshold": 0.05,
                "observed_signal_strength": 0.04,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["interpretation_outcome"] == "BRIDGE_SIGNAL_INTERNAL_ONLY"


def test_interpretation_reports_insufficient_hold_for_weak_signal(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_INTERPRETATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, signal_threshold=0.20, signal_strength=0.17)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["interpretation_outcome"] == "BRIDGE_SIGNAL_INSUFFICIENT_HOLD"