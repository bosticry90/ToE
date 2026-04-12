from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_regime_limit_alignment_attack_retry_packet_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_row": "ROW-PILLAR-GR-001",
            "required_inputs": {
                "gr_regime_limit_alignment_attack_packet_declaration": "formal/docs/release/GR_REGIME_LIMIT_ALIGNMENT_ATTACK_PACKET_20260412_v0.json",
                "gr_regime_limit_alignment_attack_packet_report": "formal/output/reports/gr_regime_limit_alignment_attack_packet_20260412_v0.json",
                "gr_regime_limit_alignment_obligation_declaration_report": "formal/output/reports/gr_regime_limit_alignment_obligation_declaration_20260412_v0.json",
                "gr_subtarget_report": "formal/output/reports/theorem_gap_gr_subtarget_tranche_20260411_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json"
            },
            "retry_binding": {
                "required_prior_packet_outcome": "GR_REGIME_LIMIT_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE",
                "required_obligation_outcome": "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED",
                "required_obligation_id": "GR_REGIME_LIMIT_TO_ALIGNMENT_BRIDGE_OBLIGATION_v0",
                "required_attack_class": "GR_REGIME_LIMIT_ALIGNMENT_ATTACK",
                "required_target_row": "ROW-PILLAR-GR-001",
                "single_retry_only": True,
                "single_ruling_only": True
            },
            "ruling_contract": {
                "allowed_outcomes": [
                    "GR_BLOCKER_MOVED",
                    "GR_VALID_BUT_NONMOVING",
                    "GR_PATH_FALSIFIED",
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_REGIME_LIMIT_ALIGNMENT_RETRY_OUTCOME",
                "no_loop_rule": "ONE_GR_REGIME_LIMIT_ALIGNMENT_RETRY_PACKET_ONLY",
                "default_outcome": "GR_PATH_FALSIFIED"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    prior_packet_outcome: str = "GR_REGIME_LIMIT_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE",
    obligation_outcome: str = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED",
    obligation_id: str = "GR_REGIME_LIMIT_TO_ALIGNMENT_BRIDGE_OBLIGATION_v0",
    retry_justified: bool = True,
    theorem_gap_delta: int = 0,
    row_success_incremented: bool = False,
    row_success_count: int = 0,
    blocker_state_change: str = "NO_DELTA_DETECTED_ROUTE_TO_REWORK",
) -> None:
    _write_json(
        root / "formal" / "docs" / "release" / "GR_REGIME_LIMIT_ALIGNMENT_ATTACK_PACKET_20260412_v0.json",
        {
            "attack_class": "GR_REGIME_LIMIT_ALIGNMENT_ATTACK",
            "target_row": "ROW-PILLAR-GR-001",
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_regime_limit_alignment_attack_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": prior_packet_outcome,
                "target_row": "ROW-PILLAR-GR-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_regime_limit_alignment_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": obligation_outcome,
                "missing_obligation_id": obligation_id,
                "retry_justified": retry_justified,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_gr_subtarget_tranche_20260411_v0.json",
        {
            "objective_quality": {
                "inputs": {
                    "theorem_gap_delta": theorem_gap_delta,
                    "target_row_success_count_incremented": row_success_incremented,
                }
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {
            "objective_quality": {
                "inputs": {
                    "row_outcome_counts": {
                        "ROW-PILLAR-GR-001": {"success": row_success_count}
                    }
                }
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json",
        {"actual_blocker_state_change": blocker_state_change},
    )


def test_reports_insufficient_even_with_declared_obligation(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "GR_REGIME_LIMIT_ALIGNMENT_ATTACK_RETRY_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"


def test_reports_blocker_moved(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "GR_REGIME_LIMIT_ALIGNMENT_ATTACK_RETRY_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, theorem_gap_delta=-1)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_BLOCKER_MOVED"


def test_reports_path_falsified_when_retry_binding_is_broken(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "GR_REGIME_LIMIT_ALIGNMENT_ATTACK_RETRY_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, obligation_outcome="GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_PATH_FALSIFIED"


def test_reports_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "GR_REGIME_LIMIT_ALIGNMENT_ATTACK_RETRY_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, row_success_count=1)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_VALID_BUT_NONMOVING"
