from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import em_qft_interface_alignment_packet_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    obligation_declared: bool = False,
    signal_observed: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "em_qft_next_attack_class_selection_report": "formal/output/reports/em_qft_next_attack_class_selection_20260412_v0.json",
                "em_qft_seam_first_test_packet_report": "formal/output/reports/em_qft_seam_first_test_packet_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "science_post_qm_stat_rebalance_report": "formal/output/reports/science_post_qm_stat_rebalance_20260412_v0.json"
            },
            "alignment_policy": {
                "required_selected_attack_class": "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
                "required_target_seam": "SEAM-EM-QFT",
                "require_gr_row_001_frozen": True,
                "require_qm_stat_hold_unchanged": True,
                "em_qft_interface_alignment_obligation_declared": obligation_declared,
                "em_qft_signal_observed": signal_observed,
                "single_execution_only": True,
                "single_ruling_only": True
            },
            "ruling_contract": {
                "allowed_outcomes": [
                    "EM_QFT_SEAM_SIGNAL_PRODUCED",
                    "EM_QFT_VALID_BUT_NONMOVING",
                    "EM_QFT_PATH_FALSIFIED",
                    "EM_QFT_INTERFACE_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EM_QFT_INTERFACE_ALIGNMENT_OUTCOME",
                "no_loop_rule": "ONE_EM_QFT_INTERFACE_ALIGNMENT_PACKET_ONLY",
                "default_outcome": "EM_QFT_PATH_FALSIFIED"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    selected_attack_class: str = "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
    gr_row_frozen: bool = True,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_next_attack_class_selection_20260412_v0.json",
        {
            "summary": {
                "selected_attack_class": selected_attack_class,
                "target_seam": "SEAM-EM-QFT",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_seam_first_test_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "EM_QFT_SEAM_VALID_BUT_NONMOVING",
                "target_seam": "SEAM-EM-QFT",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {
            "summary": {
                "row_001_attack_class_cycling_frozen": gr_row_frozen,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_post_qm_stat_rebalance_20260412_v0.json",
        {
            "summary": {
                "qm_stat_bridge_state": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
            }
        },
    )


def test_reports_requires_undeclared_structure(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, obligation_declared=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_INTERFACE_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE"


def test_reports_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, obligation_declared=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_VALID_BUT_NONMOVING"


def test_reports_signal_produced(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    _write_declaration(declaration_path, obligation_declared=True, signal_observed=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_SEAM_SIGNAL_PRODUCED"


def test_reports_path_falsified_when_preconditions_break(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, selected_attack_class="EM_QFT_SIGNAL_REFINEMENT_ATTACK")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "EM_QFT_PATH_FALSIFIED"
