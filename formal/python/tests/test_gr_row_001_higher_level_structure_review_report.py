from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_row_001_higher_level_structure_review_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_row": "ROW-PILLAR-GR-001",
            "required_inputs": {
                "gr_master_action_transport_attack_retry_packet_report": "formal/output/reports/gr_master_action_transport_attack_retry_packet_20260412_v0.json",
                "gr_regime_limit_alignment_attack_retry_packet_report": "formal/output/reports/gr_regime_limit_alignment_attack_retry_packet_20260412_v0.json",
                "gr_master_action_transport_obligation_declaration_report": "formal/output/reports/gr_master_action_transport_obligation_declaration_20260412_v0.json",
                "gr_regime_limit_alignment_obligation_declaration_report": "formal/output/reports/gr_regime_limit_alignment_obligation_declaration_20260412_v0.json"
            },
            "review_policy": {
                "target_row": "ROW-PILLAR-GR-001",
                "convergence_pattern": "two_distinct_attack_families_both_declared_but_insufficient",
                "review_scope": "higher-level_structural_adequacy",
                "single_review_only": True,
                "single_outcome_only": True
            },
            "review_contract": {
                "allowed_outcomes": [
                    "HIGHER_LEVEL_GR_STRUCTURE_DECLARABLE",
                    "HIGHER_LEVEL_GR_STRUCTURE_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                    "HIGHER_LEVEL_GR_STRUCTURE_REQUIRES_HIGHER_LEVEL_POLICY",
                    "HOLD_ROW_001_AND_STOP_ATTACK_CLASS_CYCLING"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_STRUCTURE_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_GR_ROW_001_STRUCTURE_REVIEW_ONLY",
                "default_outcome": "HOLD_ROW_001_AND_STOP_ATTACK_CLASS_CYCLING"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    transport_retry_outcome: str = "GR_TRANSPORT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT",
    alignment_retry_outcome: str = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT",
    transport_obligation_outcome: str = "GR_TRANSPORT_OBLIGATION_DECLARED",
    alignment_obligation_outcome: str = "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "gr_master_action_transport_attack_retry_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": transport_retry_outcome,
                "target_row": "ROW-PILLAR-GR-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_regime_limit_alignment_attack_retry_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": alignment_retry_outcome,
                "target_row": "ROW-PILLAR-GR-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_master_action_transport_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": transport_obligation_outcome,
                "missing_obligation_id": "GR_MASTER_ACTION_TO_REGIME_LIMIT_TRANSPORT_OBLIGATION_v0",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_regime_limit_alignment_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": alignment_obligation_outcome,
                "missing_obligation_id": "GR_REGIME_LIMIT_TO_ALIGNMENT_BRIDGE_OBLIGATION_v0",
            }
        },
    )


def test_reports_hold_when_convergent_insufficient(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "GR_ROW_001_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HIGHER_LEVEL_GR_STRUCTURE_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"
    assert report["summary"]["convergent_insufficient_detected"] is True
    assert report["summary"]["next_action"] == "FREEZE_ROW_001_ATTACK_CLASS_CYCLING_AND_DEFINE_NEW_GR_SEAM_OR_MODEL_CLASS"


def test_reports_hold_when_transport_not_insufficient(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "GR_ROW_001_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, transport_retry_outcome="GR_BLOCKER_MOVED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_ROW_001_AND_STOP_ATTACK_CLASS_CYCLING"
    assert report["summary"]["convergent_insufficient_detected"] is False


def test_reports_hold_when_alignment_not_insufficient(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "GR_ROW_001_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, alignment_retry_outcome="GR_VALID_BUT_NONMOVING")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_ROW_001_AND_STOP_ATTACK_CLASS_CYCLING"
    assert report["summary"]["convergent_insufficient_detected"] is False


def test_reports_row_structure_status_requires_analysis(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "GR_ROW_001_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["objective_quality"]["summary"]["row_structure_status"] == "FROZEN_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"
