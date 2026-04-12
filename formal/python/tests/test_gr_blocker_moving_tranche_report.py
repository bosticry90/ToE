from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_blocker_moving_tranche_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_rebalance_report": "formal/output/reports/science_post_qm_stat_rebalance_20260412_v0.json",
                "execution_checkpoint": "formal/output/ws10_tgc10_gr_packet05_increment_execution_checkpoint_20260408_v0.json",
                "gr_subtarget_report": "formal/output/reports/theorem_gap_gr_subtarget_tranche_20260411_v0.json",
                "gr_stop_rule_decision_report": "formal/output/reports/theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json",
                "trend_report": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
            },
            "target_row": "ROW-PILLAR-GR-001",
            "movement_policy": {
                "success_rule": "THEOREM_GAP_DELTA_LT_0_OR_TARGET_ROW_SUCCESS_INCREMENT_GT_0_OR_BLOCKER_STATE_TOKEN_CHANGED",
                "nonmoving_rule": "ALL_MOVEMENT_SIGNALS_FALSE_AND_NO_ATTACK_CLASS_MISMATCH",
                "different_attack_class_rule": "STOP_RULE_TRIGGERED_AND_DECISION_DEFER_OR_RECLASSIFY",
                "falsification_rule": "EXECUTION_PRECONDITIONS_BROKEN_OR_SCOPE_MISMATCH",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
            },
            "classification_contract": {
                "allowed_outcomes": [
                    "GR_BLOCKER_MOVED",
                    "GR_VALID_BUT_NONMOVING",
                    "GR_PATH_FALSIFIED",
                    "GR_REQUIRES_DIFFERENT_ATTACK_CLASS",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_BLOCKER_OUTCOME",
                "default_outcome": "GR_VALID_BUT_NONMOVING",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    rebalance_outcome: str = "ACTIVATE_GR_BLOCKER_MOVING_TRANCHE",
    subtarget_row: str = "ROW-PILLAR-GR-001",
    theorem_gap_prior: int = 7,
    theorem_gap_current: int = 7,
    row_success: int = 0,
    blocker_state_change: str = "NO_DELTA_DETECTED_ROUTE_TO_REWORK",
    stop_triggered: bool = True,
    stop_decision: str = "DEFER_OR_RECLASSIFY_GR_NEAR_TERM_BLOCKER_BURN_LANE",
    checkpoint_failed: int = 0,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_post_qm_stat_rebalance_20260412_v0.json",
        {"summary": {"selected_outcome": rebalance_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "ws10_tgc10_gr_packet05_increment_execution_checkpoint_20260408_v0.json",
        {
            "evidence": {"passed": 7, "failed": checkpoint_failed},
            "packet05_matrix_drift_detected": False,
            "seam_coupling_regression_detected": False,
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_gr_subtarget_tranche_20260411_v0.json",
        {"objective_quality": {"inputs": {"target_row": subtarget_row}}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json",
        {"summary": {"stop_rule_triggered": stop_triggered, "decision": stop_decision}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json",
        {"blocker_counts": {"prior": {"THEOREM_GAP": theorem_gap_prior}, "current": {"THEOREM_GAP": theorem_gap_current}}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {"objective_quality": {"inputs": {"row_outcome_counts": {"ROW-PILLAR-GR-001": {"success": row_success}}}}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json",
        {"actual_blocker_state_change": blocker_state_change},
    )


def test_gr_tranche_reports_requires_different_attack_class(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_BLOCKER_MOVING_TRANCHE_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["tranche_classification"] == "GR_REQUIRES_DIFFERENT_ATTACK_CLASS"


def test_gr_tranche_reports_blocker_moved(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_BLOCKER_MOVING_TRANCHE_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, theorem_gap_current=6, stop_triggered=False, stop_decision="")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["tranche_classification"] == "GR_BLOCKER_MOVED"


def test_gr_tranche_reports_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_BLOCKER_MOVING_TRANCHE_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, stop_triggered=False, stop_decision="")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["tranche_classification"] == "GR_VALID_BUT_NONMOVING"


def test_gr_tranche_reports_path_falsified_on_precondition_break(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_BLOCKER_MOVING_TRANCHE_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, rebalance_outcome="HOLD_AND_REQUIRE_RESCORING")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["tranche_classification"] == "GR_PATH_FALSIFIED"
