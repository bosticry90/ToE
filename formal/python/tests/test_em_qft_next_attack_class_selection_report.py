from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import em_qft_next_attack_class_selection_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_refinement: bool = False,
    subseam_reselection: bool = False,
    interface_alignment: bool = True,
    rescoring: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "em_qft_post_first_test_decision_report": "formal/output/reports/em_qft_post_first_test_decision_20260412_v0.json",
                "em_qft_seam_first_test_packet_report": "formal/output/reports/em_qft_seam_first_test_packet_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "science_post_qm_stat_rebalance_report": "formal/output/reports/science_post_qm_stat_rebalance_20260412_v0.json"
            },
            "selection_policy": {
                "required_decision_outcome": "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS",
                "required_first_test_outcome": "EM_QFT_SEAM_VALID_BUT_NONMOVING",
                "required_target_seam": "SEAM-EM-QFT",
                "require_gr_row_001_frozen": True,
                "require_qm_stat_hold_unchanged": True,
                "signal_refinement_priority": signal_refinement,
                "subseam_reselection_priority": subseam_reselection,
                "interface_alignment_priority": interface_alignment,
                "require_rescoring": rescoring,
                "single_selection_only": True,
                "single_outcome_only": True
            },
            "selection_contract": {
                "allowed_outcomes": [
                    "EM_QFT_SIGNAL_REFINEMENT_ATTACK",
                    "EM_QFT_SUBSEAM_TARGET_RESELECTION_ATTACK",
                    "EM_QFT_INTERFACE_ALIGNMENT_ATTACK",
                    "HOLD_EM_QFT_AND_REQUIRE_RESCORING"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_EM_QFT_NEXT_ATTACK_CLASS_OUTCOME",
                "no_loop_rule": "ONE_EM_QFT_NEXT_ATTACK_CLASS_SELECTION_ONLY",
                "default_outcome": "HOLD_EM_QFT_AND_REQUIRE_RESCORING"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    decision_outcome: str = "EM_QFT_REQUIRES_DIFFERENT_ATTACK_CLASS",
    first_test_outcome: str = "EM_QFT_SEAM_VALID_BUT_NONMOVING",
    gr_frozen: bool = True,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_post_first_test_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": decision_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_seam_first_test_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": first_test_outcome, "target_seam": "SEAM-EM-QFT"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {"summary": {"row_001_attack_class_cycling_frozen": gr_frozen}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_post_qm_stat_rebalance_20260412_v0.json",
        {"summary": {"qm_stat_bridge_state": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"}},
    )


def test_reports_interface_alignment_by_default(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_attack_class"] == "EM_QFT_INTERFACE_ALIGNMENT_ATTACK"


def test_reports_signal_refinement_when_prioritized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
    _write_declaration(declaration_path, signal_refinement=True, interface_alignment=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_attack_class"] == "EM_QFT_SIGNAL_REFINEMENT_ATTACK"


def test_reports_subseam_reselection_when_prioritized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
    _write_declaration(declaration_path, subseam_reselection=True, interface_alignment=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_attack_class"] == "EM_QFT_SUBSEAM_TARGET_RESELECTION_ATTACK"


def test_reports_hold_and_rescore_when_preconditions_break(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "EM_QFT_NEXT_ATTACK_CLASS_SELECTION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, gr_frozen=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_attack_class"] == "HOLD_EM_QFT_AND_REQUIRE_RESCORING"
