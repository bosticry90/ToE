from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import em_qft_interface_alignment_retry_packet_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path, *, signal_observed: bool = False) -> None:
    _write_json(
        path,
        {
            "target_seam": "SEAM-EM-QFT",
            "required_inputs": {
                "em_qft_interface_alignment_packet_declaration": "formal/docs/release/EM_QFT_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json",
                "em_qft_interface_alignment_packet_report": "formal/output/reports/em_qft_interface_alignment_packet_20260412_v0.json",
                "em_qft_interface_alignment_obligation_declaration_report": "formal/output/reports/em_qft_interface_alignment_obligation_declaration_20260412_v0.json",
                "em_qft_next_attack_class_selection_report": "formal/output/reports/em_qft_next_attack_class_selection_20260412_v0.json"
            },
            "retry_binding": {
                "required_prior_packet_outcome": "EM_QFT_INTERFACE_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE",
                "required_obligation_outcome": "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED",
                "required_obligation_id": "EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_OBLIGATION_v0",
                "required_attack_class": "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
                "required_target_seam": "SEAM-EM-QFT",
                "em_qft_signal_observed": signal_observed,
                "single_retry_only": True,
                "single_ruling_only": True
            },
            "ruling_contract": {
                "allowed_outcomes": [
                    "EM_QFT_SEAM_SIGNAL_PRODUCED",
                    "EM_QFT_VALID_BUT_NONMOVING",
                    "EM_QFT_PATH_FALSIFIED",
                    "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EM_QFT_INTERFACE_ALIGNMENT_RETRY_OUTCOME",
                "no_loop_rule": "ONE_EM_QFT_INTERFACE_ALIGNMENT_RETRY_PACKET_ONLY",
                "default_outcome": "EM_QFT_PATH_FALSIFIED"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    prior_packet_outcome: str = "EM_QFT_INTERFACE_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE",
    obligation_outcome: str = "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED",
    selected_attack_class: str = "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
) -> None:
    _write_json(
        root / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json",
        {
            "attack_class": "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
            "target_seam": "SEAM-EM-QFT",
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_interface_alignment_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": prior_packet_outcome,
                "target_seam": "SEAM-EM-QFT",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_interface_alignment_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": obligation_outcome,
                "missing_obligation_id": "EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_OBLIGATION_v0",
                "retry_justified": True,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_next_attack_class_selection_20260412_v0.json",
        {
            "summary": {
                "selected_attack_class": selected_attack_class,
                "target_seam": "SEAM-EM-QFT",
            }
        },
    )


def test_reports_declared_but_still_insufficient_by_default(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_RETRY_PACKET_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"


def test_reports_signal_produced_when_observed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_RETRY_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, signal_observed=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_SEAM_SIGNAL_PRODUCED"


def test_reports_path_falsified_when_binding_is_broken(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_RETRY_PACKET_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, selected_attack_class="EM_QFT_SIGNAL_REFINEMENT_ATTACK")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_PATH_FALSIFIED"


def test_reports_path_falsified_when_obligation_not_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_RETRY_PACKET_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, obligation_outcome="EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_PATH_FALSIFIED"
