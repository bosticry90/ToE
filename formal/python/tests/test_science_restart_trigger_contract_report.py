from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_restart_trigger_contract_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    trigger_overrides: dict | None = None,
    include_full_signal_shape: bool = True,
) -> None:
    trigger_families = {
        "stronger_candidate_class_identified": False,
        "higher_level_policy_revision_authorized": False,
        "material_new_external_evidence_class": False,
        "anti_alias_proof_for_new_candidate_declared": False,
        "force_policy_escalation_now": False,
    }
    if trigger_overrides:
        trigger_families.update(trigger_overrides)
    if not include_full_signal_shape:
        trigger_families.pop("force_policy_escalation_now")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_post_phase_z_frontier_decision_report": "formal/output/reports/science_post_phase_z_frontier_decision_20260412_v0.json",
                "science_phase_z_stronger_candidate_class_discovery_report": "formal/output/reports/science_phase_z_stronger_candidate_class_discovery_20260412_v0.json",
                "science_frontier_stop_state_summary_doc": "formal/docs/release/SCIENCE_FRONTIER_STOP_STATE_SUMMARY_20260412_v0.md",
                "science_restart_higher_level_policy_trigger_report": "formal/output/reports/science_restart_higher_level_policy_trigger_20260413_v0.json",
            },
            "restart_trigger_contract": {
                "required_post_phase_z_outcome": "PRESERVE_CURRENT_GOVERNED_STOP_STATE",
                "required_phase_z_outcome": "NO_STRONGER_CANDIDATE_CLASS_IDENTIFIED_YET",
                "required_lane_reopen_authorized": False,
                "required_new_lane_or_packet_authorized_now": False,
                "required_thermal_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
                "required_higher_level_policy_trigger_outcome": "HIGHER_LEVEL_POLICY_REVISION_NOT_AUTHORIZED",
                "required_higher_level_policy_revision_authorized": False,
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "restart_trigger_families": trigger_families,
            },
            "restart_trigger_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_RESTART_TRIGGER_CONTRACT_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_RESTART_TRIGGER_CONTRACT_LAYER_ONLY",
                "allowed_outcomes": [
                    "REMAIN_IN_GOVERNED_STOP_STATE",
                    "OPEN_ONE_BOUNDED_PRE_SCREENING_RESTART_GATE",
                    "RESTART_TRIGGER_CONTRACT_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RESTART_TRIGGER_CONTRACT_REPAIR",
                ],
                "default_outcome": "RESTART_TRIGGER_CONTRACT_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_z_outcome: str = "NO_STRONGER_CANDIDATE_CLASS_IDENTIFIED_YET",
    higher_level_policy_trigger_outcome: str = "HIGHER_LEVEL_POLICY_REVISION_NOT_AUTHORIZED",
    higher_level_policy_revision_authorized: bool = False,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_post_phase_z_frontier_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "PRESERVE_CURRENT_GOVERNED_STOP_STATE",
                "lane_specific_reopen_authorized": False,
                "new_lane_or_packet_authorized_now": False,
                "thermal_boundary_lane_status": "PRESERVED_INACTIVE_NEAR_READY_NOT_EXECUTABLE",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_z_stronger_candidate_class_discovery_20260412_v0.json",
        {"summary": {"terminal_outcome": phase_z_outcome}},
    )
    _write_text(
        root / "formal" / "docs" / "release" / "SCIENCE_FRONTIER_STOP_STATE_SUMMARY_20260412_v0.md",
        "No currently governed lane is authorized to reopen.\n"
        "No currently screened future candidate is authorized for active execution.\n",
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_higher_level_policy_trigger_20260413_v0.json",
        {
            "summary": {
                "terminal_outcome": higher_level_policy_trigger_outcome,
                "higher_level_policy_revision_authorized": higher_level_policy_revision_authorized,
            }
        },
    )


def test_reports_remain_in_governed_stop_state(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_TRIGGER_CONTRACT_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REMAIN_IN_GOVERNED_STOP_STATE"


def test_reports_open_one_bounded_pre_screening_restart_gate(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_TRIGGER_CONTRACT_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        trigger_overrides={
            "stronger_candidate_class_identified": True,
            "anti_alias_proof_for_new_candidate_declared": True,
        },
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "OPEN_ONE_BOUNDED_PRE_SCREENING_RESTART_GATE"


def test_reports_hold_pending_restart_trigger_contract_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_TRIGGER_CONTRACT_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_signal_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RESTART_TRIGGER_CONTRACT_REPAIR"


def test_reports_restart_trigger_contract_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_TRIGGER_CONTRACT_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        trigger_overrides={"material_new_external_evidence_class": True},
    )
    _seed_inputs(tmp_path, phase_z_outcome="STRONGER_CANDIDATE_CLASS_DISCOVERY_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RESTART_TRIGGER_CONTRACT_EVIDENCE_INCOMPLETE"
