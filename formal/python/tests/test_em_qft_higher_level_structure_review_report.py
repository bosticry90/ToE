from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import em_qft_higher_level_structure_review_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    declareable: bool = False,
    requires_new_seam: bool = True,
    requires_policy: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "em_qft_seam_first_test_packet_report": "formal/output/reports/em_qft_seam_first_test_packet_20260412_v0.json",
                "em_qft_post_first_test_decision_report": "formal/output/reports/em_qft_post_first_test_decision_20260412_v0.json",
                "em_qft_interface_alignment_packet_report": "formal/output/reports/em_qft_interface_alignment_packet_20260412_v0.json",
                "em_qft_interface_alignment_obligation_declaration_report": "formal/output/reports/em_qft_interface_alignment_obligation_declaration_20260412_v0.json",
                "em_qft_interface_alignment_retry_packet_report": "formal/output/reports/em_qft_interface_alignment_retry_packet_20260412_v0.json"
            },
            "review_policy": {
                "target_seam": "SEAM-EM-QFT",
                "freeze_attack_class_cycling_for_seam": True,
                "declareable_within_current_scope": declareable,
                "requires_new_seam_or_model_class": requires_new_seam,
                "requires_higher_level_policy": requires_policy,
                "single_review_only": True,
                "single_outcome_only": True
            },
            "review_contract": {
                "allowed_outcomes": [
                    "EM_QFT_HIGHER_LEVEL_STRUCTURE_DECLARABLE",
                    "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                    "EM_QFT_REQUIRES_HIGHER_LEVEL_POLICY",
                    "HOLD_EM_QFT_AND_STOP_ATTACK_CLASS_CYCLING"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_ONLY",
                "default_outcome": "HOLD_EM_QFT_AND_STOP_ATTACK_CLASS_CYCLING"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    retry_outcome: str = "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_seam_first_test_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": "EM_QFT_SEAM_VALID_BUT_NONMOVING", "target_seam": "SEAM-EM-QFT"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_post_first_test_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS", "target_seam": "SEAM-EM-QFT"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_interface_alignment_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": "EM_QFT_INTERFACE_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE", "target_seam": "SEAM-EM-QFT"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_interface_alignment_obligation_declaration_20260412_v0.json",
        {"summary": {"terminal_outcome": "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED", "obligation_type": "THEOREM_LINKED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_interface_alignment_retry_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": retry_outcome, "target_seam": "SEAM-EM-QFT"}},
    )


def test_reports_requires_new_seam_or_model_class(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"


def test_reports_higher_level_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
    _write_declaration(declaration_path, requires_policy=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_REQUIRES_HIGHER_LEVEL_POLICY"


def test_reports_declarable(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
    _write_declaration(declaration_path, declareable=True, requires_new_seam=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_HIGHER_LEVEL_STRUCTURE_DECLARABLE"


def test_reports_hold_when_convergence_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_HIGHER_LEVEL_STRUCTURE_REVIEW_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, retry_outcome="EM_QFT_VALID_BUT_NONMOVING")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_EM_QFT_AND_STOP_ATTACK_CLASS_CYCLING"
