from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_post_hardening_probe_execution_refresh_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_signal_margin_hardening_cycle_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_cycle_20260422_v0.json",
                "bridge_probe_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "refresh_policy": {
                "required_cycle_outcome": "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD",
                "required_cycle_executed": True,
                "not_a_multi_cycle": True,
                "no_scope_expansion": True,
            },
            "refresh_contract": {
                "allowed_outcomes": [
                    "POST_HARDENING_PROBE_EXECUTION_REFRESHED",
                    "POST_HARDENING_PROBE_EXECUTION_UNCHANGED",
                    "POST_HARDENING_PROBE_EXECUTION_REFRESH_PRECONDITION_FAILED",
                    "POST_HARDENING_PROBE_EXECUTION_REFRESH_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_HARDENING_PROBE_EXECUTION_REFRESH_OUTCOME",
                "no_loop_rule": "ONE_POST_HARDENING_PROBE_EXECUTION_REFRESH_ONLY",
                "default_outcome": "POST_HARDENING_PROBE_EXECUTION_REFRESH_PRECONDITION_FAILED",
            },
        },
    )


def _seed_cycle_report(
    root: Path,
    *,
    cycle_outcome: str = "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD",
    cycle_executed: bool = True,
    post_signal_margin: float = 0.05,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_cycle_20260422_v0.json",
        {
            "summary": {
                "cycle_outcome": cycle_outcome,
                "cycle_executed": cycle_executed,
                "signal_margin": post_signal_margin,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            },
            "objective_quality": {"inputs": {"post_signal_margin": post_signal_margin}},
        },
    )


def _seed_probe_execution(
    root: Path,
    *,
    prior_signal_margin: float = 0.04,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "PROBE_SIGNAL_CONFIRMED",
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": prior_signal_margin,
            },
            "objective_quality": {
                "inputs": {
                    "probe_signal_strength": 0.11,
                    "probe_signal_threshold": 0.07,
                    "probe_discrimination_threshold": 0.02,
                    "path_falsification_observed": False,
                }
            },
        },
    )


def test_refreshes_probe_execution_when_cycle_executed_to_threshold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_HARDENING_PROBE_EXECUTION_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path, post_signal_margin=0.05)
    _seed_probe_execution(tmp_path, prior_signal_margin=0.04)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "POST_HARDENING_PROBE_EXECUTION_REFRESHED"
    assert report["summary"]["inputs_changed"] is True
    assert report["summary"]["signal_margin"] == pytest.approx(0.05, abs=1e-9)
    assert report["summary"]["prior_signal_margin"] == pytest.approx(0.04, abs=1e-9)


def test_refresh_unchanged_when_post_margin_equals_prior(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_HARDENING_PROBE_EXECUTION_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path, post_signal_margin=0.04)
    _seed_probe_execution(tmp_path, prior_signal_margin=0.04)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["refresh_outcome"] == "POST_HARDENING_PROBE_EXECUTION_UNCHANGED"
    assert report["summary"]["inputs_changed"] is False


def test_precondition_failed_when_cycle_outcome_not_required(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_HARDENING_PROBE_EXECUTION_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(
        tmp_path,
        cycle_outcome="SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_PARTIAL",
    )
    _seed_probe_execution(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["refresh_outcome"]
        == "POST_HARDENING_PROBE_EXECUTION_REFRESH_PRECONDITION_FAILED"
    )
    assert report["criteria"]["cycle_outcome_matches_required"] is False


def test_scope_violation_when_seam_binding_mismatch(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_HARDENING_PROBE_EXECUTION_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path)
    _seed_probe_execution(tmp_path, comparator_id="OV-RL-10-ALT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["refresh_outcome"]
        == "POST_HARDENING_PROBE_EXECUTION_REFRESH_SCOPE_VIOLATION"
    )
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False


def test_refresh_preserves_terminal_outcome_and_non_claim_guards(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_HARDENING_PROBE_EXECUTION_REFRESH_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_cycle_report(tmp_path)
    _seed_probe_execution(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "PROBE_SIGNAL_CONFIRMED"
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True
