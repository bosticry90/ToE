from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_master_action_transport_attack_packet_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path, *, obligation_declared: bool = False) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "gr_subtarget_declaration": "formal/docs/release/THEOREM_GAP_GR_SUBTARGET_TRANCHE_20260411_v0.json",
                "gr_subtarget_report": "formal/output/reports/theorem_gap_gr_subtarget_tranche_20260411_v0.json",
                "gr_stop_rule_decision_report": "formal/output/reports/theorem_gap_gr_bounded_stop_rule_decision_20260411_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
                "master_action_transport_surface_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json"
            },
            "target_row": "ROW-PILLAR-GR-001",
            "transport_policy": {
                "gr_master_action_transport_obligation_declared": obligation_declared,
                "require_reclassification_signal": True,
                "require_no_delta_signal": True,
                "single_execution_only": True,
                "single_ruling_only": True
            },
            "ruling_contract": {
                "allowed_outcomes": [
                    "GR_BLOCKER_MOVED",
                    "GR_VALID_BUT_NONMOVING",
                    "GR_PATH_FALSIFIED",
                    "GR_MASTER_ACTION_TRANSPORT_REQUIRES_UNDECLARED_STRUCTURE"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_MASTER_ACTION_TRANSPORT_OUTCOME",
                "no_loop_rule": "ONE_GR_MASTER_ACTION_TRANSPORT_PACKET_ONLY",
                "default_outcome": "GR_VALID_BUT_NONMOVING"
            }
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
    attack_class: str = "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
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
    _write_json(
        root / "formal" / "output" / "reports" / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
        {"attack_class": attack_class},
    )


def test_reports_requires_undeclared_structure(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, obligation_declared=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_MASTER_ACTION_TRANSPORT_REQUIRES_UNDECLARED_STRUCTURE"


def test_reports_blocker_moved(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, obligation_declared=True)
    _seed_inputs(tmp_path, theorem_gap_delta=-1)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_BLOCKER_MOVED"


def test_reports_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, obligation_declared=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_VALID_BUT_NONMOVING"


def test_reports_path_falsified_when_preconditions_break(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, obligation_declared=True)
    _seed_inputs(tmp_path, report_target_row="ROW-PILLAR-QFT-001")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_PATH_FALSIFIED"
