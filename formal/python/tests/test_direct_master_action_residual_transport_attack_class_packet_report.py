from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    direct_master_action_residual_transport_attack_class_packet_report as packet_tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def test_direct_master_action_packet_materializes_qm_stat_target(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
            "packet_id": "DMART-001",
            "required_inputs": {
                "science_next_attack_class_selection_report": "formal/output/reports/science_next_attack_class_selection_20260411_v0.json",
                "proof_debt_program_exhaustion_decision_report": "formal/output/reports/proof_debt_program_exhaustion_decision_20260411_v0.json",
                "qm_blocker_moving_ruling_report": "formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json",
                "broader_seam_package_redesign_decision_report": "formal/output/reports/broader_seam_package_redesign_decision_20260411_v0.json",
                "seam_registry_surface": "formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md",
                "closure_map_report": "formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
                "current_target_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
            },
            "failure_synthesis_scope": {
                "must_include_prior_classes": [
                    "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
                    "QM_BLOCKER_MOVING_TRANCHE",
                    "BROADER_SEAM_PACKAGE_REDESIGN",
                ]
            },
            "new_attack_hypothesis": {
                "hypothesis_id": "HYP-DMART-001",
                "statement": "direct package",
                "mechanism": "one bounded package",
            },
            "single_bounded_target": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "blocker_class": "SEAM_INTEGRATION_GAP",
                "owning_lane": "QM_STAT_CYCLE11",
                "target_kind": "UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
                "required_closure_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                "required_evidence_surface": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
                "selection_reason": "registry blocker matches target kind",
            },
            "success_failure_measurement": {
                "success_rule": "BLOCKER_DELTA_LT_0_OR_SEAM_INTEGRATION_GAP_DELTA_LT_0_OR_TARGET_ROW_SUCCESS_INCREMENT_GT_0_OR_BLOCKER_TOKEN_CHANGE_TRUE",
                "failure_rule": "ALL_MOVEMENT_SIGNALS_FALSE",
                "no_loop_rule": "ONE_BOUNDED_PACKET_ONLY",
                "movement_signals": ["SEAM_INTEGRATION_GAP_DELTA_LT_0"],
            },
        },
    )
    _write_json(
        reports_dir / "science_next_attack_class_selection_20260411_v0.json",
        {
            "summary": {
                "decision": "ESCALATE_TO_DECLARED_NEXT_ATTACK_CLASS",
                "selected_next_attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
                "next_action": "MATERIALIZE_DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET",
                "proof_debt_parallel_reopen_allowed": False,
            }
        },
    )
    _write_json(
        reports_dir / "proof_debt_program_exhaustion_decision_20260411_v0.json",
        {"summary": {"program_state": "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER", "decision": "ESCALATE_TO_NEXT_ATTACK_CLASS"}},
    )
    _write_json(
        reports_dir / "qm_blocker_moving_ruling_20260411_v0.json",
        {"summary": {"qm_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER", "tranche_classification": "QM_VALID_BUT_NONMOVING"}},
    )
    _write_json(
        reports_dir / "broader_seam_package_redesign_decision_20260411_v0.json",
        {"summary": {"decision": "BROADER_SEAM_REDESIGN_NONPRODUCTIVE_IN_BOUNDED_TRANCHE", "packet_outcome": "SEAM_REDESIGN_NO_BLOCKER_MOVEMENT", "blocker_facing_movement_observed": False}},
    )
    _write_text(
        tmp_path / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md",
        "\n".join(
            [
                "- `SEAM_QM_STAT_GOVERNANCE_COMPLETE_v0: NO`",
                "- `SEAM_QM_STAT_PHYSICS_COMPLETE_v0: NO`",
                "- `SEAM_QM_STAT_STATUS_READ_v0: CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE`",
                "- `SEAM_QM_STAT_PHYSICS_BLOCKER_v0: NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE`",
            ]
        ),
    )
    _write_json(
        reports_dir / "governance_blocker_closure_map_20260410_v0.json",
        {
            "mappings": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                    "owning_lane": "QM_STAT_CYCLE11",
                    "required_closure_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                    "required_evidence_surface": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
                }
            ]
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"status": "CRITERIA_AND_EIGHTEENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM", "adjudication": {"value": "NOT_YET_DISCHARGED"}},
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_MATERIALIZED"
    assert report["summary"]["selected_target_row"] == "ROW-SEAM-QM-STAT-001"
    assert report["summary"]["selected_target_package_id"] == "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
    assert report["summary"]["next_action"] == "EXECUTE_DIRECT_MASTER_ACTION_QM_STAT_TRANSPORT_RESIDUAL_PACKET_ONCE"
    assert report["single_bounded_target"]["seam_physics_blocker"] == "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"


def test_direct_master_action_packet_fails_closed_when_target_alignment_is_missing(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
            "packet_id": "DMART-001",
            "required_inputs": {
                "science_next_attack_class_selection_report": "formal/output/reports/science_next_attack_class_selection_20260411_v0.json",
                "proof_debt_program_exhaustion_decision_report": "formal/output/reports/proof_debt_program_exhaustion_decision_20260411_v0.json",
                "qm_blocker_moving_ruling_report": "formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json",
                "broader_seam_package_redesign_decision_report": "formal/output/reports/broader_seam_package_redesign_decision_20260411_v0.json",
                "seam_registry_surface": "formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md",
                "closure_map_report": "formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
                "current_target_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
            },
            "failure_synthesis_scope": {},
            "new_attack_hypothesis": {"hypothesis_id": "HYP-DMART-001"},
            "single_bounded_target": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "blocker_class": "SEAM_INTEGRATION_GAP",
                "owning_lane": "QM_STAT_CYCLE11",
                "target_kind": "UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
            },
            "success_failure_measurement": {
                "failure_rule": "ALL_MOVEMENT_SIGNALS_FALSE",
                "no_loop_rule": "ONE_BOUNDED_PACKET_ONLY",
            },
        },
    )
    _write_json(
        reports_dir / "science_next_attack_class_selection_20260411_v0.json",
        {
            "summary": {
                "decision": "ESCALATE_TO_DECLARED_NEXT_ATTACK_CLASS",
                "selected_next_attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
                "next_action": "MATERIALIZE_DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET",
                "proof_debt_parallel_reopen_allowed": False,
            }
        },
    )
    _write_json(
        reports_dir / "proof_debt_program_exhaustion_decision_20260411_v0.json",
        {"summary": {"program_state": "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER"}},
    )
    _write_json(
        reports_dir / "qm_blocker_moving_ruling_20260411_v0.json",
        {"summary": {"qm_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER", "tranche_classification": "QM_VALID_BUT_NONMOVING"}},
    )
    _write_json(
        reports_dir / "broader_seam_package_redesign_decision_20260411_v0.json",
        {"summary": {"decision": "BROADER_SEAM_REDESIGN_NONPRODUCTIVE_IN_BOUNDED_TRANCHE", "packet_outcome": "SEAM_REDESIGN_NO_BLOCKER_MOVEMENT", "blocker_facing_movement_observed": False}},
    )
    _write_text(
        tmp_path / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md",
        "\n".join(
            [
                "- `SEAM_QM_STAT_GOVERNANCE_COMPLETE_v0: NO`",
                "- `SEAM_QM_STAT_PHYSICS_COMPLETE_v0: NO`",
                "- `SEAM_QM_STAT_STATUS_READ_v0: CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE`",
                "- `SEAM_QM_STAT_PHYSICS_BLOCKER_v0: NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE`",
            ]
        ),
    )
    _write_json(reports_dir / "governance_blocker_closure_map_20260410_v0.json", {"mappings": []})
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"status": "CRITERIA_AND_EIGHTEENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM", "adjudication": {"value": "NOT_YET_DISCHARGED"}},
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "DIRECT_MASTER_ACTION_ATTACK_CLASS_PACKET_INCOMPLETE"
    assert report["summary"]["next_action"] == "REVIEW_SELECTION_OR_TARGET_ALIGNMENT_ONCE"
