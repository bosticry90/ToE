from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_row_001_structural_gap_definition_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path, *, declareable: bool = False, requires_new_seam: bool = True, requires_policy: bool = False) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "gr_master_action_transport_attack_retry_packet_report": "formal/output/reports/gr_master_action_transport_attack_retry_packet_20260412_v0.json",
                "gr_regime_limit_alignment_attack_retry_packet_report": "formal/output/reports/gr_regime_limit_alignment_attack_retry_packet_20260412_v0.json",
                "gr_master_action_transport_obligation_declaration_report": "formal/output/reports/gr_master_action_transport_obligation_declaration_20260412_v0.json",
                "gr_regime_limit_alignment_obligation_declaration_report": "formal/output/reports/gr_regime_limit_alignment_obligation_declaration_20260412_v0.json"
            },
            "structural_gap_policy": {
                "target_row": "ROW-PILLAR-GR-001",
                "freeze_attack_class_cycling_for_row": True,
                "declareable_within_current_gr_scope": declareable,
                "requires_new_gr_seam_or_model_class": requires_new_seam,
                "requires_higher_level_policy": requires_policy,
                "single_review_only": True,
                "single_outcome_only": True
            },
            "review_contract": {
                "allowed_outcomes": [
                    "GR_HIGHER_LEVEL_STRUCTURE_DECLARABLE",
                    "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                    "GR_REQUIRES_HIGHER_LEVEL_POLICY",
                    "HOLD_ROW_001_UNTIL_NEW_STRUCTURE_EXISTS"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_ROW_001_STRUCTURAL_GAP_OUTCOME",
                "no_loop_rule": "ONE_GR_ROW_001_STRUCTURAL_GAP_DEFINITION_ONLY",
                "default_outcome": "HOLD_ROW_001_UNTIL_NEW_STRUCTURE_EXISTS"
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
    target_row: str = "ROW-PILLAR-GR-001",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "gr_master_action_transport_attack_retry_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": transport_retry_outcome, "target_row": target_row}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_regime_limit_alignment_attack_retry_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": alignment_retry_outcome, "target_row": target_row}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_master_action_transport_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": transport_obligation_outcome,
                "obligation_type": "THEOREM_LINKED"
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_regime_limit_alignment_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": alignment_obligation_outcome,
                "obligation_type": "THEOREM_LINKED"
            }
        },
    )


def test_reports_requires_new_seam_or_model_class(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_STRUCTURAL_GAP_DEFINITION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"


def test_reports_higher_level_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_STRUCTURAL_GAP_DEFINITION_20260412_v0.json"
    _write_declaration(declaration_path, requires_policy=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_REQUIRES_HIGHER_LEVEL_POLICY"


def test_reports_declarable(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_STRUCTURAL_GAP_DEFINITION_20260412_v0.json"
    _write_declaration(declaration_path, declareable=True, requires_new_seam=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_HIGHER_LEVEL_STRUCTURE_DECLARABLE"


def test_reports_hold_when_convergence_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_ROW_001_STRUCTURAL_GAP_DEFINITION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, alignment_retry_outcome="GR_VALID_BUT_NONMOVING")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_ROW_001_UNTIL_NEW_STRUCTURE_EXISTS"
