from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_cross_probe_consistency_confirmation_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_significance_inputs_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_significance_inputs_refresh_20260422_v0.json",
                "bridge_probe_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
                "bridge_probe_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "confirmation_policy": {
                "required_significance_outcome": "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
                "required_execution_terminal_outcome": "PROBE_SIGNAL_CONFIRMED",
                "required_ruling_terminal_outcome": "PROBE_SIGNAL_CONFIRMED",
                "required_ruling_status": "TERMINAL_OUTCOME_CONFIRMED",
                "require_comparator_repeatability_confirmed": True,
                "not_a_new_probe_cycle": True,
                "no_scope_expansion": True,
            },
            "confirmation_contract": {
                "allowed_outcomes": [
                    "CROSS_PROBE_CONSISTENCY_CONFIRMED",
                    "CROSS_PROBE_CONSISTENCY_UNCHANGED",
                    "CROSS_PROBE_CONSISTENCY_PRECONDITION_FAILED",
                    "CROSS_PROBE_CONSISTENCY_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_CROSS_PROBE_CONSISTENCY_CONFIRMATION_OUTCOME",
                "no_loop_rule": "ONE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_ONLY",
                "default_outcome": "CROSS_PROBE_CONSISTENCY_UNCHANGED",
            },
        },
    )


def _seed_significance_inputs(
    root: Path,
    *,
    adjudication_outcome: str = "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
    comparator_repeatability_confirmed: bool = True,
    cross_probe_consistency_confirmed: bool = False,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_significance_inputs_refresh_20260422_v0.json",
        {
            "summary": {
                "adjudication_outcome": adjudication_outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": 0.04,
            },
            "objective_quality": {
                "inputs": {
                    "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                    "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                    "signal_margin": 0.04,
                    "external_path_success_signal_margin_min": 0.05,
                    "confirmed_but_limited_signal_margin_min": 0.02,
                    "one_more_cycle_signal_margin_min": 0.0,
                }
            },
        },
    )


def _seed_probe_execution(
    root: Path,
    *,
    terminal_outcome: str = "PROBE_SIGNAL_CONFIRMED",
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
                "terminal_outcome": terminal_outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": 0.04,
            }
        },
    )


def _seed_probe_ruling(
    root: Path,
    *,
    terminal_outcome: str = "PROBE_SIGNAL_CONFIRMED",
    ruling_status: str = "TERMINAL_OUTCOME_CONFIRMED",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": terminal_outcome,
                "ruling_status": ruling_status,
            }
        },
    )


def test_confirms_cross_probe_consistency_when_all_preconditions_hold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_inputs(tmp_path, comparator_repeatability_confirmed=True)
    _seed_probe_execution(tmp_path)
    _seed_probe_ruling(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["confirmation_outcome"] == "CROSS_PROBE_CONSISTENCY_CONFIRMED"
    assert report["summary"]["cross_probe_consistency_confirmed_updated_to"] is True
    assert report["objective_quality"]["inputs"]["cross_probe_consistency_confirmed"] is True
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True


def test_reports_unchanged_when_already_confirmed(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_inputs(tmp_path, cross_probe_consistency_confirmed=True)
    _seed_probe_execution(tmp_path)
    _seed_probe_ruling(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["confirmation_outcome"] == "CROSS_PROBE_CONSISTENCY_UNCHANGED"
    assert report["summary"]["inputs_changed"] is False


def test_precondition_failed_when_repeatability_not_confirmed(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_inputs(tmp_path, comparator_repeatability_confirmed=False)
    _seed_probe_execution(tmp_path)
    _seed_probe_ruling(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["confirmation_outcome"] == "CROSS_PROBE_CONSISTENCY_PRECONDITION_FAILED"
    assert report["criteria"]["comparator_repeatability_precondition_matches"] is False


def test_precondition_failed_when_probe_execution_not_confirmed(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_inputs(tmp_path)
    _seed_probe_execution(tmp_path, terminal_outcome="PROBE_SIGNAL_INCONCLUSIVE")
    _seed_probe_ruling(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["confirmation_outcome"] == "CROSS_PROBE_CONSISTENCY_PRECONDITION_FAILED"
    assert report["criteria"]["execution_outcome_matches_required"] is False


def test_scope_violation_when_observed_scope_mismatches_declaration(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_significance_inputs(tmp_path)
    _seed_probe_execution(tmp_path, comparator_id="OV-RL-10-ALT")
    _seed_probe_ruling(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["confirmation_outcome"] == "CROSS_PROBE_CONSISTENCY_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False
