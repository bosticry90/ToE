from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_z_stronger_candidate_class_discovery_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_overrides: dict | None = None,
    include_full_signal_shape: bool = True,
) -> None:
    discovery_signals = {
        "candidate_class_structural_properties_defined": True,
        "candidate_class_observable_interface_requirements_defined": True,
        "candidate_class_exclusion_patterns_defined": True,
        "stronger_candidate_class_named": False,
        "higher_level_policy_revision_needed": False,
        "maintain_governed_stop_state": False,
    }
    if signal_overrides:
        discovery_signals.update(signal_overrides)
    if not include_full_signal_shape:
        discovery_signals.pop("maintain_governed_stop_state")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_y_post_comparative_synthesis_decision_report": "formal/output/reports/science_phase_y_post_comparative_synthesis_decision_20260412_v0.json",
                "science_phase_x_governed_lane_end_comparative_synthesis_report": "formal/output/reports/science_phase_x_governed_lane_end_comparative_synthesis_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "stronger_candidate_class_discovery_contract": {
                "required_phase_y_outcome": "WAIT_FOR_STRONGER_CANDIDATE_CLASS",
                "required_phase_x_outcome": "GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_COMPLETE",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_thermal_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
                "required_thermal_no_further_closure_authorized": True,
                "required_thermal_packet_authorized": False,
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "discovery_signals": discovery_signals,
            },
            "stronger_candidate_class_discovery_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_LAYER_ONLY",
                "allowed_outcomes": [
                    "STRONGER_CANDIDATE_CLASS_IDENTIFIED",
                    "NO_STRONGER_CANDIDATE_CLASS_IDENTIFIED_YET",
                    "REQUIRES_HIGHER_LEVEL_POLICY_REVISION",
                    "MAINTAIN_CURRENT_GOVERNED_STOP_STATE",
                    "STRONGER_CANDIDATE_CLASS_DISCOVERY_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_STRONGER_CANDIDATE_CLASS_DISCOVERY_REPAIR",
                ],
                "default_outcome": "STRONGER_CANDIDATE_CLASS_DISCOVERY_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_y_outcome: str = "WAIT_FOR_STRONGER_CANDIDATE_CLASS",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_y_post_comparative_synthesis_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_y_outcome,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_x_governed_lane_end_comparative_synthesis_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "GOVERNED_LANE_END_COMPARATIVE_SYNTHESIS_COMPLETE",
                "thermal_boundary_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
                "thermal_boundary_no_further_closure_authorized": True,
                "thermal_boundary_packet_authorized": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
            }
        },
    )


def test_reports_no_stronger_candidate_class_identified_yet(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "NO_STRONGER_CANDIDATE_CLASS_IDENTIFIED_YET"


def test_reports_stronger_candidate_class_identified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={"stronger_candidate_class_named": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "STRONGER_CANDIDATE_CLASS_IDENTIFIED"


def test_reports_requires_higher_level_policy_revision(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={"higher_level_policy_revision_needed": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REQUIRES_HIGHER_LEVEL_POLICY_REVISION"


def test_reports_maintain_current_governed_stop_state(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        signal_overrides={"maintain_governed_stop_state": True},
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "MAINTAIN_CURRENT_GOVERNED_STOP_STATE"


def test_reports_hold_pending_stronger_candidate_class_discovery_repair(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_signal_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["terminal_outcome"]
        == "HOLD_PENDING_STRONGER_CANDIDATE_CLASS_DISCOVERY_REPAIR"
    )


def test_reports_stronger_candidate_class_discovery_evidence_incomplete(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_Z_STRONGER_CANDIDATE_CLASS_DISCOVERY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_y_outcome="POST_COMPARATIVE_DECISION_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert (
        report["summary"]["terminal_outcome"]
        == "STRONGER_CANDIDATE_CLASS_DISCOVERY_EVIDENCE_INCOMPLETE"
    )
