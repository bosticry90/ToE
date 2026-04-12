from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import proof_debt_program_exhaustion_decision_report as decision_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _base_declaration(*, specific_filter_defect_identified: bool, bounded_filter_revision_packet: str | None) -> dict:
    return {
        "current_attack_class": "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
        "required_inputs": {
            "current_attack_class_decision_report": "formal/output/reports/fundamental_attack_strategy_rethink_decision_20260411_v0.json",
            "next_cluster_selection_report": "formal/output/reports/proof_debt_next_cluster_selection_report_20260411_v0.json",
            "cluster_focus_reports": [
                "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_math_pd_burndown_20260411_v0.json",
                "formal/output/reports/proof_debt_active_cluster_next_tranche_focus_emu1_distributional_auth_20260411_v0.json",
            ],
            "surface_ruling_reports": [
                "formal/output/reports/proof_debt_active_cluster_surface_ruling_math_pd_c05_burndown_gate_20260411_v0.json",
                "formal/output/reports/proof_debt_active_cluster_surface_ruling_emu1_micro22_semantics_mapping_gate_20260411_v0.json",
            ],
        },
        "decision_policy": {
            "specific_filter_defect_identified": specific_filter_defect_identified,
            "specific_filter_defect_note": (
                "selector weights undercount sequential prerequisite surfaces"
                if specific_filter_defect_identified
                else None
            ),
            "bounded_filter_revision_packet": bounded_filter_revision_packet,
            "next_attack_class_if_escalated": "NEW_ATTACK_CLASS_REQUIRED",
            "surface_run_hold_policy": "NO_FURTHER_SURFACE_RUNS_UNTIL_DECISION_PACKET_RESOLVED",
        },
    }


def _surface_ruling_payload(cluster_id: str, surface_id: str) -> dict:
    return {
        "cluster_id": cluster_id,
        "summary": {
            "surface_id": surface_id,
            "surface_ruling": "SURFACE_EXECUTED_VALID_NO_BLOCKER_MOVEMENT",
            "gate_passed": True,
            "exclude_from_immediate_reselection": True,
            "blocker_facing_movement_observed": False,
        },
        "objective_quality": {
            "inputs": {
                "movement_signals": {
                    "theorem_gap_state_changed": False,
                    "seam_integration_state_changed": False,
                    "global_row_success_state_changed": False,
                    "blocker_state_token_changed": False,
                }
            }
        },
    }


def test_program_exhaustion_defaults_to_attack_class_escalation(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(decision_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROOF_DEBT_PROGRAM_EXHAUSTION_DECISION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        _base_declaration(specific_filter_defect_identified=False, bounded_filter_revision_packet=None),
    )
    _write_json(
        reports_dir / "fundamental_attack_strategy_rethink_decision_20260411_v0.json",
        {"summary": {"selected_next_experimental_class": "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN"}},
    )
    _write_json(
        reports_dir / "proof_debt_next_cluster_selection_report_20260411_v0.json",
        {
            "summary": {
                "selection_outcome": "NO_ELIGIBLE_CLUSTER_UNDER_CURRENT_FILTER",
                "next_action": "ESCALATE_TO_NEXT_SCIENCE_ATTACK_CLASS",
                "exhausted_from_active_surface_selector": [
                    "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
                    "PDC-EMU1-DISTRIBUTIONAL-AUTH-01",
                ],
            }
        },
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_next_tranche_focus_math_pd_burndown_20260411_v0.json",
        {"cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01", "summary": {"selection_outcome": "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE"}},
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_next_tranche_focus_emu1_distributional_auth_20260411_v0.json",
        {"cluster_id": "PDC-EMU1-DISTRIBUTIONAL-AUTH-01", "summary": {"selection_outcome": "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE"}},
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_surface_ruling_math_pd_c05_burndown_gate_20260411_v0.json",
        _surface_ruling_payload("PDC-MATH-PROOF-DEBT-BURNDOWN-01", "MATH-PD-C05-BURNDOWN-GATE"),
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_surface_ruling_emu1_micro22_semantics_mapping_gate_20260411_v0.json",
        _surface_ruling_payload("PDC-EMU1-DISTRIBUTIONAL-AUTH-01", "EMU1-MICRO22-SEMANTICS-MAPPING-GATE"),
    )

    report = decision_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["program_state"] == "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"
    assert report["summary"]["decision"] == "ESCALATE_TO_NEXT_ATTACK_CLASS"
    assert report["summary"]["filter_revision_status"] == "NO_SPECIFIC_FILTER_DEFECT_IDENTIFIED"
    assert report["summary"]["next_action"] == "MATERIALIZE_ONE_NEW_ATTACK_CLASS_PACKET"
    assert report["summary"]["selected_next_attack_class"] is None
    assert report["summary"]["next_attack_class_status"] == "NEW_ATTACK_CLASS_REQUIRED"
    assert report["summary"]["tested_surface_count"] == 2


def test_program_exhaustion_can_route_to_bounded_filter_revision(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(decision_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "PROOF_DEBT_PROGRAM_EXHAUSTION_DECISION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        _base_declaration(
            specific_filter_defect_identified=True,
            bounded_filter_revision_packet="formal/docs/release/PROOF_DEBT_FILTER_REVISION_PACKET_20260411_v0.json",
        ),
    )
    _write_json(
        reports_dir / "fundamental_attack_strategy_rethink_decision_20260411_v0.json",
        {"summary": {"selected_next_experimental_class": "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN"}},
    )
    _write_json(
        reports_dir / "proof_debt_next_cluster_selection_report_20260411_v0.json",
        {
            "summary": {
                "selection_outcome": "NO_ELIGIBLE_CLUSTER_UNDER_CURRENT_FILTER",
                "exhausted_from_active_surface_selector": [
                    "PDC-MATH-PROOF-DEBT-BURNDOWN-01",
                    "PDC-EMU1-DISTRIBUTIONAL-AUTH-01",
                ],
            }
        },
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_next_tranche_focus_math_pd_burndown_20260411_v0.json",
        {"cluster_id": "PDC-MATH-PROOF-DEBT-BURNDOWN-01", "summary": {"selection_outcome": "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE"}},
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_next_tranche_focus_emu1_distributional_auth_20260411_v0.json",
        {"cluster_id": "PDC-EMU1-DISTRIBUTIONAL-AUTH-01", "summary": {"selection_outcome": "NO_ELIGIBLE_ACTIVE_CLUSTER_SURFACE"}},
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_surface_ruling_math_pd_c05_burndown_gate_20260411_v0.json",
        _surface_ruling_payload("PDC-MATH-PROOF-DEBT-BURNDOWN-01", "MATH-PD-C05-BURNDOWN-GATE"),
    )
    _write_json(
        reports_dir / "proof_debt_active_cluster_surface_ruling_emu1_micro22_semantics_mapping_gate_20260411_v0.json",
        _surface_ruling_payload("PDC-EMU1-DISTRIBUTIONAL-AUTH-01", "EMU1-MICRO22-SEMANTICS-MAPPING-GATE"),
    )

    report = decision_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["program_state"] == "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"
    assert report["summary"]["decision"] == "EXECUTE_FILTER_REVISION_PACKET_ONCE"
    assert report["summary"]["filter_revision_status"] == "FILTER_REVISION_JUSTIFIED_AND_BOUNDED"
    assert report["summary"]["next_action"] == "EXECUTE_FILTER_REVISION_PACKET_ONCE"
    assert report["summary"]["selected_next_attack_class"] is None
