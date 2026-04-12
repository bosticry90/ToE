from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_limitation_review_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_probe_significance_adjudication_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_20260412_v0.json",
                "bridge_probe_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
                "bridge_probe_ruling_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "diagnosis_policy": {
                "external_path_success_signal_margin_min": 0.05,
                "auto_authorize_additional_cycle": False,
            },
            "review_contract": {
                "allowed_outcomes": [
                    "LIMITATION_LOCAL_REFINABLE_ONE_MORE_BOUNDED_COMPARATOR_CYCLE_JUSTIFIED",
                    "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD",
                    "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD",
                    "LIMITATION_INTERPRETATION_SCOPE_HOLD",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_LIMITATION_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_LIMITATION_REVIEW_ONLY",
                "default_outcome": "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    significance_outcome: str = "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
    execution_outcome: str = "PROBE_SIGNAL_CONFIRMED",
    ruling_status: str = "TERMINAL_OUTCOME_CONFIRMED",
    ruling_outcome: str = "PROBE_SIGNAL_CONFIRMED",
    signal_margin: float = 0.04,
    comparator_repeatability_confirmed: bool = False,
    cross_probe_consistency_confirmed: bool = False,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_20260412_v0.json",
        {
            "summary": {
                "adjudication_outcome": significance_outcome,
            },
            "objective_quality": {
                "inputs": {
                    "external_path_success_signal_margin_min": 0.05,
                    "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                    "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": execution_outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": signal_margin,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json",
        {
            "summary": {
                "ruling_status": ruling_status,
                "terminal_outcome": ruling_outcome,
            }
        },
    )


def test_limitation_review_reports_one_more_cycle_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        significance_outcome="PROBE_SIGNAL_REQUIRES_ONE_MORE_BOUNDED_COMPARATOR_CYCLE",
        execution_outcome="PROBE_SIGNAL_NONDISCRIMINATIVE",
        ruling_outcome="PROBE_SIGNAL_NONDISCRIMINATIVE",
        signal_margin=0.01,
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["review_outcome"]
        == "LIMITATION_LOCAL_REFINABLE_ONE_MORE_BOUNDED_COMPARATOR_CYCLE_JUSTIFIED"
    )
    assert report["summary"]["one_more_bounded_comparator_cycle_justified"] is True


def test_limitation_review_reports_comparator_bound_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        significance_outcome="PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
        comparator_repeatability_confirmed=False,
        cross_probe_consistency_confirmed=False,
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD"


def test_limitation_review_reports_signal_margin_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        significance_outcome="PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
        signal_margin=0.03,
        comparator_repeatability_confirmed=True,
        cross_probe_consistency_confirmed=True,
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD"


def test_limitation_review_reports_interpretation_scope_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        significance_outcome="PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
        comparator_id="OV-RL-11",
    )
    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "LIMITATION_INTERPRETATION_SCOPE_HOLD"
