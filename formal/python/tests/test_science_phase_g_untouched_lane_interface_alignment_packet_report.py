from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_g_untouched_lane_interface_alignment_packet_report as tool


_CANONICAL_ANTI_ALIAS = {
    "QM-STAT": True,
    "GR-ROW-001": True,
    "EM-QFT": True,
    "SHARED-MODEL-CLASS": True,
    "QFT-GR": True,
}


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_detected: bool = False,
    alignment_valid_without_movement: bool = True,
    undeclared_structure_detected: bool = False,
    anti_alias_checks: dict[str, bool] | None = None,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_d_untouched_lane_selection_report": "formal/output/reports/science_phase_d_untouched_lane_selection_20260412_v0.json",
                "science_phase_f_untouched_lane_attack_class_reselection_report": "formal/output/reports/science_phase_f_untouched_lane_attack_class_reselection_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "packet_policy": {
                "required_phase_d_selection_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "required_phase_f_reselection_outcome": "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_selected_untouched_lane": "LANE-NEUTRINO-INTERFACE-001",
                "required_selected_attack_class": "neutrino_interface_alignment_boundary_probe",
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
                "selected_attack_class": "neutrino_interface_alignment_boundary_probe",
                "one_execution_only": True,
                "one_immediate_ruling_only": True,
                "signal_detected": signal_detected,
                "alignment_valid_without_movement": alignment_valid_without_movement,
                "undeclared_structure_detected": undeclared_structure_detected,
                "anti_alias_checks": anti_alias_checks if anti_alias_checks is not None else dict(_CANONICAL_ANTI_ALIAS),
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "packet_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_LAYER_ONLY",
                "allowed_outcomes": [
                    "UNTOUCHED_LANE_SIGNAL_PRODUCED",
                    "UNTOUCHED_LANE_VALID_BUT_NONMOVING",
                    "UNTOUCHED_LANE_REQUIRES_UNDECLARED_STRUCTURE",
                    "UNTOUCHED_LANE_PATH_FALSIFIED",
                ],
                "default_outcome": "UNTOUCHED_LANE_PATH_FALSIFIED",
            },
        },
    )


def _seed_inputs(root: Path, *, phase_f_outcome: str = "UNTOUCHED_LANE_INTERFACE_ALIGNMENT_ATTACK") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_d_untouched_lane_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "untouched_lane_candidate_id": "LANE-NEUTRINO-INTERFACE-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_f_untouched_lane_attack_class_reselection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_f_outcome,
                "selected_next_attack_class": "neutrino_interface_alignment_boundary_probe",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_VALID_BUT_NONMOVING"


def test_reports_signal_produced(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path, signal_detected=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_SIGNAL_PRODUCED"


def test_reports_requires_undeclared_structure(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path, undeclared_structure_detected=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_REQUIRES_UNDECLARED_STRUCTURE"


def test_reports_path_falsified_when_anti_alias_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    )
    anti_alias = dict(_CANONICAL_ANTI_ALIAS)
    anti_alias["QM-STAT"] = False
    _write_declaration(declaration_path, anti_alias_checks=anti_alias)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_PATH_FALSIFIED"


def test_reports_path_falsified_when_phase_f_precondition_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_G_UNTOUCHED_LANE_INTERFACE_ALIGNMENT_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_f_outcome="HOLD_UNTOUCHED_LANE_AND_STOP")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_PATH_FALSIFIED"
