from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_cycle_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    planned_margin_uplift: float = 0.01,
    max_single_cycle_margin_uplift: float = 0.01,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_signal_margin_hardening_slice_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_slice_20260422_v0.json"
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "execution_policy": {
                "required_slice_outcome": "SIGNAL_MARGIN_HARDENING_SLICE_READY",
                "required_hardening_ready": True,
                "not_a_multi_cycle": True,
                "no_scope_expansion": True,
                "planned_margin_uplift": planned_margin_uplift,
                "max_single_cycle_margin_uplift": max_single_cycle_margin_uplift,
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD",
                    "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_PARTIAL",
                    "SIGNAL_MARGIN_HARDENING_CYCLE_PRECONDITION_FAILED",
                    "SIGNAL_MARGIN_HARDENING_CYCLE_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SIGNAL_MARGIN_HARDENING_CYCLE_OUTCOME",
                "no_loop_rule": "ONE_SIGNAL_MARGIN_HARDENING_CYCLE_ONLY",
                "default_outcome": "SIGNAL_MARGIN_HARDENING_CYCLE_PRECONDITION_FAILED",
            },
        },
    )


def _seed_slice_report(
    root: Path,
    *,
    slice_outcome: str = "SIGNAL_MARGIN_HARDENING_SLICE_READY",
    hardening_ready: bool = True,
    signal_margin: float = 0.04,
    success_margin_min: float = 0.05,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
    observed_comparator_id: str = "OV-RL-10",
    observed_quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_slice_20260422_v0.json",
        {
            "summary": {
                "slice_outcome": slice_outcome,
                "hardening_ready": hardening_ready,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": success_margin_min,
                "margin_gap_to_success_threshold": max(success_margin_min - signal_margin, 0.0),
            },
            "objective_quality": {
                "inputs": {
                    "signal_margin": signal_margin,
                    "external_path_success_signal_margin_min": success_margin_min,
                    "margin_gap_to_success_threshold": max(success_margin_min - signal_margin, 0.0),
                    "observed_comparator_id": observed_comparator_id,
                    "observed_quantity_id": observed_quantity_id,
                }
            },
        },
    )


def test_cycle_executes_and_advances_to_threshold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_CYCLE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_slice_report(tmp_path, signal_margin=0.04, success_margin_min=0.05)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["cycle_outcome"]
        == "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD"
    )
    assert report["summary"]["cycle_executed"] is True
    assert report["summary"]["signal_margin"] == pytest.approx(0.05, abs=1e-9)
    assert report["summary"]["remaining_gap_to_success_threshold"] == pytest.approx(0.0, abs=1e-9)


def test_cycle_executes_partial_when_uplift_is_smaller_than_gap(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_CYCLE_20260422_v0.json"
    )
    _write_declaration(declaration_path, planned_margin_uplift=0.005, max_single_cycle_margin_uplift=0.005)
    _seed_slice_report(tmp_path, signal_margin=0.04, success_margin_min=0.05)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["cycle_outcome"]
        == "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_PARTIAL"
    )
    assert report["summary"]["signal_margin"] == pytest.approx(0.045, abs=1e-9)
    assert report["summary"]["remaining_gap_to_success_threshold"] == pytest.approx(0.005, abs=1e-9)


def test_precondition_failed_when_slice_not_ready(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_CYCLE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_slice_report(tmp_path, slice_outcome="SIGNAL_MARGIN_HARDENING_SLICE_PRECONDITION_FAILED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["cycle_outcome"] == "SIGNAL_MARGIN_HARDENING_CYCLE_PRECONDITION_FAILED"
    assert report["criteria"]["slice_outcome_matches_required"] is False


def test_precondition_failed_when_hardening_not_ready(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_CYCLE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_slice_report(tmp_path, hardening_ready=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["cycle_outcome"] == "SIGNAL_MARGIN_HARDENING_CYCLE_PRECONDITION_FAILED"
    assert report["criteria"]["hardening_ready_matches_required"] is False


def test_scope_violation_when_observed_scope_mismatch(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_CYCLE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_slice_report(tmp_path, observed_comparator_id="OV-RL-10-ALT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["cycle_outcome"] == "SIGNAL_MARGIN_HARDENING_CYCLE_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False
