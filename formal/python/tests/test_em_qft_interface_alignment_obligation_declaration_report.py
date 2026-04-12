from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import em_qft_interface_alignment_obligation_declaration_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "em_qft_interface_alignment_packet_report": "formal/output/reports/em_qft_interface_alignment_packet_20260412_v0.json",
                "em_qft_next_attack_class_selection_report": "formal/output/reports/em_qft_next_attack_class_selection_20260412_v0.json"
            },
            "obligation_policy": {
                "target_seam": "SEAM-EM-QFT",
                "required_attack_class": "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
                "missing_obligation_id": "EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_OBLIGATION_v0",
                "missing_obligation_statement": "SEAM-EM-QFT interface-alignment route requires explicit interface bridge obligation linking EM witness alignment constraints to QFT seam dispatch semantics.",
                "obligation_type": "THEOREM_LINKED",
                "scope_violation_detected": False,
                "requires_higher_level_policy": False,
                "obligation_justified": True,
                "obligation_declared": True
            },
            "declaration_contract": {
                "allowed_outcomes": [
                    "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED",
                    "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_REQUIRES_HIGHER_LEVEL_POLICY",
                    "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_OUT_OF_SCOPE",
                    "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARATION_OUTCOME",
                "no_loop_rule": "ONE_EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARATION_ONLY",
                "default_outcome": "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    packet_outcome: str = "EM_QFT_INTERFACE_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE",
    selected_attack_class: str = "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
    target_seam: str = "SEAM-EM-QFT",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_interface_alignment_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": packet_outcome,
                "target_seam": target_seam,
                "attack_class": "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_next_attack_class_selection_20260412_v0.json",
        {
            "summary": {
                "selected_attack_class": selected_attack_class,
                "target_seam": target_seam,
            }
        },
    )


def test_reports_obligation_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED"


def test_reports_out_of_scope(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, target_seam="SEAM-GR-QM")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_OUT_OF_SCOPE"


def test_reports_not_justified_when_selection_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, selected_attack_class="EM_QFT_SIGNAL_REFINEMENT_ATTACK")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED"


def test_reports_retry_justified_true_when_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["retry_justified"] is True
