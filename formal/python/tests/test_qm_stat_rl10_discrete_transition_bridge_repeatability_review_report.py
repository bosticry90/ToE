from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_repeatability_review_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path, *, repeatability_check_named: bool = False, cross_probe_check_named: bool = False, path_falsification_observed: bool = False) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_limitation_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_limitation_review_20260412_v0.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "repeatability_policy": {
                "required_limitation_cause": "comparator_repeatability_or_cross_probe_consistency_not_yet_confirmed",
                "required_local_and_refinable": True,
                "repeatability_check_named": repeatability_check_named,
                "cross_probe_consistency_check_named": cross_probe_check_named,
                "path_falsification_observed": path_falsification_observed,
            },
            "review_contract": {
                "allowed_outcomes": [
                    "REPEATABILITY_CHECK_JUSTIFIED",
                    "CROSS_PROBE_CONSISTENCY_CHECK_JUSTIFIED",
                    "LIMITED_HOLD_RETAINED",
                    "PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_REPEATABILITY_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_REPEATABILITY_REVIEW_ONLY",
                "default_outcome": "LIMITED_HOLD_RETAINED",
            },
        },
    )


def _seed_limitation_review(root: Path, *, review_outcome: str = "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD", local_and_refinable: bool = True, one_more_cycle: bool = False, comparator_id: str = "OV-RL-10", quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_limitation_review_20260412_v0.json",
        {
            "summary": {
                "review_outcome": review_outcome,
                "limitation_primary_cause": "comparator_repeatability_or_cross_probe_consistency_not_yet_confirmed",
                "local_and_refinable": local_and_refinable,
                "one_more_bounded_comparator_cycle_justified": one_more_cycle,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
                "signal_margin": 0.04,
                "next_action": "KEEP_SEAM_ACTIVE_AS_LIMITED_AND_PREPARE_BOUNDED_LIMITATION_HARDENING",
            }
        },
    )


def test_repeatability_review_reports_limited_hold_retained(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal" / "docs" / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_limitation_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "LIMITED_HOLD_RETAINED"
    assert report["summary"]["bounded_check_possible_without_full_cycle"] is False


def test_repeatability_review_reports_repeatability_check_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal" / "docs" / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path, repeatability_check_named=True)
    _seed_limitation_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "REPEATABILITY_CHECK_JUSTIFIED"
    assert report["summary"]["bounded_check_possible_without_full_cycle"] is True


def test_repeatability_review_reports_cross_probe_consistency_check_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal" / "docs" / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path, cross_probe_check_named=True)
    _seed_limitation_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "CROSS_PROBE_CONSISTENCY_CHECK_JUSTIFIED"
    assert report["summary"]["bounded_check_possible_without_full_cycle"] is True


def test_repeatability_review_reports_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal" / "docs" / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path, path_falsification_observed=True)
    _seed_limitation_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "PATH_FALSIFIED"
