from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_slice_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_limitation_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_limitation_review_20260422_v1.json",
                "bridge_probe_execution_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "hardening_policy": {
                "required_limitation_review_outcome": "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD",
                "required_limitation_primary_cause": "signal_margin_below_external_path_success_threshold",
                "require_comparator_repeatability_confirmed": True,
                "require_cross_probe_consistency_confirmed": True,
                "not_a_new_comparator_cycle": True,
                "no_scope_expansion": True,
            },
            "hardening_contract": {
                "allowed_outcomes": [
                    "SIGNAL_MARGIN_HARDENING_SLICE_READY",
                    "SIGNAL_MARGIN_HARDENING_SLICE_NOT_REQUIRED",
                    "SIGNAL_MARGIN_HARDENING_SLICE_PRECONDITION_FAILED",
                    "SIGNAL_MARGIN_HARDENING_SLICE_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SIGNAL_MARGIN_HARDENING_SLICE_OUTCOME",
                "no_loop_rule": "ONE_SIGNAL_MARGIN_HARDENING_SLICE_ONLY",
                "default_outcome": "SIGNAL_MARGIN_HARDENING_SLICE_PRECONDITION_FAILED",
            },
        },
    )


def _seed_limitation_review(
    root: Path,
    *,
    review_outcome: str = "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD",
    limitation_primary_cause: str = "signal_margin_below_external_path_success_threshold",
    signal_margin: float = 0.04,
    success_margin_min: float = 0.05,
    comparator_repeatability_confirmed: bool = True,
    cross_probe_consistency_confirmed: bool = True,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_review_20260422_v1.json",
        {
            "summary": {
                "review_outcome": review_outcome,
                "limitation_primary_cause": limitation_primary_cause,
                "signal_margin": signal_margin,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            },
            "objective_quality": {
                "inputs": {
                    "signal_margin": signal_margin,
                    "external_path_success_signal_margin_min": success_margin_min,
                    "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                    "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                }
            },
        },
    )


def _seed_probe_execution(
    root: Path,
    *,
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
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": 0.04,
            }
        },
    )


def test_slice_ready_when_signal_margin_gap_remains(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_SLICE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(tmp_path, signal_margin=0.04, success_margin_min=0.05)
    _seed_probe_execution(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["slice_outcome"] == "SIGNAL_MARGIN_HARDENING_SLICE_READY"
    assert report["summary"]["hardening_ready"] is True
    assert report["summary"]["margin_gap_to_success_threshold"] == pytest.approx(0.01, abs=1e-9)
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True


def test_slice_not_required_when_margin_at_success_threshold(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_SLICE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(tmp_path, signal_margin=0.05, success_margin_min=0.05)
    _seed_probe_execution(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["slice_outcome"] == "SIGNAL_MARGIN_HARDENING_SLICE_NOT_REQUIRED"
    assert report["summary"]["hardening_ready"] is False


def test_precondition_failed_when_limitation_outcome_wrong(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_SLICE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(tmp_path, review_outcome="LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD")
    _seed_probe_execution(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["slice_outcome"] == "SIGNAL_MARGIN_HARDENING_SLICE_PRECONDITION_FAILED"
    assert report["criteria"]["limitation_review_outcome_matches_required"] is False


def test_scope_violation_when_observed_scope_mismatch(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_SLICE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(tmp_path)
    _seed_probe_execution(tmp_path, comparator_id="OV-RL-10-ALT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["slice_outcome"] == "SIGNAL_MARGIN_HARDENING_SLICE_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False


def test_precondition_failed_when_cross_probe_consistency_not_confirmed(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_SLICE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(tmp_path, cross_probe_consistency_confirmed=False)
    _seed_probe_execution(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["slice_outcome"] == "SIGNAL_MARGIN_HARDENING_SLICE_PRECONDITION_FAILED"
    assert report["criteria"]["cross_probe_consistency_confirmed_matches_required"] is False
