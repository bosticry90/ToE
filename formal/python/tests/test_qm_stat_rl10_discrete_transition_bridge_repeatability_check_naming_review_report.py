from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    proposed_check_kind: str = "NONE",
    proposed_check_name: str = "",
    bounded_scope_declared: bool = False,
    not_full_cycle_declared: bool = False,
    path_hold_triggered: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_repeatability_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_review_20260412_v0.json",
                "bridge_first_named_repeatability_check_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json"
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "naming_policy": {
                "proposed_check_kind": proposed_check_kind,
                "proposed_check_name": proposed_check_name,
                "bounded_scope_declared": bounded_scope_declared,
                "not_disguised_second_full_cycle_declared": not_full_cycle_declared,
                "path_hold_triggered": path_hold_triggered,
            },
            "review_contract": {
                "allowed_outcomes": [
                    "BOUNDED_REPEATABILITY_CHECK_NAMED",
                    "BOUNDED_CROSS_PROBE_CHECK_NAMED",
                    "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
                    "PATH_HOLD_CONTINUES",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_REPEATABILITY_CHECK_NAMING_OUTCOME",
                "no_loop_rule": "ONE_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_ONLY",
                "default_outcome": "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
            },
        },
    )


def _seed_repeatability_review(
    root: Path,
    *,
    review_outcome: str = "LIMITED_HOLD_RETAINED",
    bounded_check_possible_without_full_cycle: bool = False,
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_repeatability_review_20260412_v0.json",
        {
            "summary": {
                "review_outcome": review_outcome,
                "bounded_check_possible_without_full_cycle": bounded_check_possible_without_full_cycle,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            }
        },
    )
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_EVIDENCE_INCOMPLETE",
                "proposed_check_kind": "",
                "proposed_check_name": "",
                "bounded_scope_declared": False,
                "not_disguised_second_full_cycle_declared": False,
                "path_hold_triggered": False,
            }
        },
    )


def test_naming_review_reports_repeatability_check_named(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        proposed_check_kind="REPEATABILITY",
        proposed_check_name="rl10_probe_repeatability_window_check_v0",
        bounded_scope_declared=True,
        not_full_cycle_declared=True,
    )
    _seed_repeatability_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "BOUNDED_REPEATABILITY_CHECK_NAMED"


def test_naming_review_reports_cross_probe_check_named(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        proposed_check_kind="CROSS_PROBE",
        proposed_check_name="rl10_bridge_cross_probe_consistency_slice_check_v0",
        bounded_scope_declared=True,
        not_full_cycle_declared=True,
    )
    _seed_repeatability_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "BOUNDED_CROSS_PROBE_CHECK_NAMED"


def test_naming_review_reports_no_specific_check_justified_yet(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_repeatability_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "NO_SPECIFIC_CHECK_JUSTIFIED_YET"


def test_naming_review_uses_named_check_package_when_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_repeatability_review(tmp_path)
    _write_json(
        tmp_path
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED",
                "proposed_check_kind": "REPEATABILITY",
                "proposed_check_name": "rl10_bridge_sigma_db_repeatability_window_check_v0",
                "bounded_scope_declared": True,
                "not_disguised_second_full_cycle_declared": True,
                "path_hold_triggered": False,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "BOUNDED_REPEATABILITY_CHECK_NAMED"
    assert report["objective_quality"]["inputs"]["named_check_admissible"] is True


def test_naming_review_reports_path_hold_continues(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path, path_hold_triggered=True)
    _seed_repeatability_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["review_outcome"] == "PATH_HOLD_CONTINUES"


def test_naming_review_exposes_named_check_admissible_in_inputs(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        proposed_check_kind="REPEATABILITY",
        proposed_check_name="rl10_probe_repeatability_window_check_v0",
        bounded_scope_declared=True,
        not_full_cycle_declared=True,
    )
    _seed_repeatability_review(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["objective_quality"]["inputs"]["named_check_admissible"] is True
