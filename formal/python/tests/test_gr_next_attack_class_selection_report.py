from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_next_attack_class_selection_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "gr_subtarget_declaration": "formal/docs/release/THEOREM_GAP_GR_SUBTARGET_TRANCHE_20260411_v0.json",
                "gr_subtarget_report": "formal/output/reports/theorem_gap_gr_subtarget_tranche_20260411_v0.json",
                "gr_stop_rule_decision_report": "formal/output/reports/theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
            },
            "selection_policy": {
                "target_row": "ROW-PILLAR-GR-001",
                "require_stop_rule_reclassification_signal": True,
                "require_gr_tranche_no_delta_signal": True,
                "prefer_master_action_transport_when_no_delta_and_reclassification": True,
                "prefer_weak_field_when_row_success_incremented": True,
                "prefer_regime_limit_when_blocker_state_changed_without_gap_delta": True,
                "fallback_to_seam_interface_when_scope_conflict": True,
                "default_attack_class": "GR_MASTER_ACTION_TRANSPORT_ATTACK",
                "default_next_action": "OPEN_SINGLE_GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET",
            },
            "selection_contract": {
                "allowed_outcomes": [
                    "GR_WEAK_FIELD_CLOSURE_ATTACK",
                    "GR_MASTER_ACTION_TRANSPORT_ATTACK",
                    "GR_REGIME_LIMIT_ALIGNMENT_ATTACK",
                    "GR_SEAM_INTERFACE_ATTACK",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_NEXT_ATTACK_CLASS",
                "no_loop_rule": "ONE_GR_ATTACK_CLASS_SELECTION_ONLY",
                "default_outcome": "GR_MASTER_ACTION_TRANSPORT_ATTACK",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    decl_target_row: str = "ROW-PILLAR-GR-001",
    report_target_row: str = "ROW-PILLAR-GR-001",
    theorem_gap_delta: int = 0,
    row_success_incremented: bool = False,
    row_success_count: int = 0,
    stop_decision: str = "DEFER_OR_RECLASSIFY_GR_NEAR_TERM_BLOCKER_BURN_LANE",
    blocker_state_change: str = "NO_DELTA_DETECTED_ROUTE_TO_REWORK",
) -> None:
    _write_json(
        root / "formal" / "docs" / "release" / "THEOREM_GAP_GR_SUBTARGET_TRANCHE_20260411_v0.json",
        {"target_row": decl_target_row},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_gr_subtarget_tranche_20260411_v0.json",
        {
            "objective_quality": {
                "inputs": {
                    "target_row": report_target_row,
                    "theorem_gap_delta": theorem_gap_delta,
                    "target_row_success_count_incremented": row_success_incremented,
                }
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json",
        {"summary": {"decision": stop_decision}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {"objective_quality": {"inputs": {"row_outcome_counts": {"ROW-PILLAR-GR-001": {"success": row_success_count}}}}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json",
        {"actual_blocker_state_change": blocker_state_change},
    )


def test_selects_master_action_transport_attack_by_default_reclassification_signal(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_attack_class"] == "GR_MASTER_ACTION_TRANSPORT_ATTACK"


def test_selects_weak_field_when_row_success_incremented(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, row_success_incremented=True, row_success_count=1, stop_decision="")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_attack_class"] == "GR_WEAK_FIELD_CLOSURE_ATTACK"


def test_selects_regime_limit_when_blocker_state_changed_without_delta(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, blocker_state_change="STATE_CHANGED_TOKEN_v0", stop_decision="")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_attack_class"] == "GR_REGIME_LIMIT_ALIGNMENT_ATTACK"


def test_selects_seam_interface_when_scope_conflict(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, report_target_row="ROW-PILLAR-QFT-001")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_attack_class"] == "GR_SEAM_INTERFACE_ATTACK"
