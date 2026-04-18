from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import master_action_packet_01_transport_binding_recovery_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "packet01_family_preservation_note": "formal/docs/paper/TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_PRESERVATION_NOTE_v0.md",
                "packet01_refinement_closeout_report": "formal/output/reports/toe_master_action_computational_analysis_packet_01_refinement_closeout_20260417_v0.json",
                "packet01_refinement_report": "formal/output/reports/toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json",
                "direct_master_action_transport_attack_class_report": "formal/output/reports/direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
                "architecture_alignment_execution_report": "formal/output/reports/architecture_seam_master_action_alignment_packet_execution_20260411_v0.json",
                "architecture_alignment_ruling_report": "formal/output/reports/architecture_seam_master_action_alignment_ruling_20260411_v0.json",
                "seam_transport_witness_binding_artifact": "formal/output/architecture/SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json",
                "master_action_residual_extraction_binding_unit_artifact": "formal/output/architecture/MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING_UNIT_v0.json",
                "seam_constraint_registry": "formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md",
                "seam_executable_path_normalization_report": "formal/output/reports/seam_executable_path_normalization_20260418_v0.json"
            },
            "recovery_policy": {
                "target_row": "ROW-SEAM-QM-STAT-001",
                "target_seam": "SEAM-QM-STAT",
                "target_transport_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
                "required_packet01_family_status": "PRESERVED_CLOSED_SUCCESS_WITHOUT_ESCALATION",
                "required_packet01_family_outcome": "RETAIN_REFINEMENT_v0",
                "required_closeout_next_action": "STOP_PACKET01_FAMILY_AND_PRESERVE_REFINED_BASELINE",
                "required_alignment_execution_classification": "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING",
                "required_alignment_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER",
                "required_transport_blocker": "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE",
                "required_qm_stat_path_class": "POLICY_BLOCKED_NONEXECUTABLE_PATH",
                "canonical_transport_read_token": "PACKET01_PRESERVED_BASELINE_PLUS_WITNESS_BINDING_PLUS_MINIMAL_UPSTREAM_UNIT_PLUS_EXPLICIT_BLOCKER"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_OUTCOME",
                "no_loop_rule": "ONE_MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_LAYER_ONLY",
                "allowed_outcomes": [
                    "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_STATE_MATERIALIZED",
                    "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_MASTER_ACTION_PACKET01_TRANSPORT_BINDING_REPAIR"
                ],
                "default_outcome": "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, policy_blocked: bool = True) -> None:
    _write_text(
        root / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_PRESERVATION_NOTE_v0.md",
        "\n".join(
            [
                "- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_STATUS_v0: PRESERVED_CLOSED_SUCCESS_WITHOUT_ESCALATION`",
                "- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_OUTCOME_v0: RETAIN_REFINEMENT_v0`",
                "- `TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_FAMILY_CANONICAL_ENDPOINT_v0: formal/output/reports/toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json`",
            ]
        ),
    )
    _write_json(
        root / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_closeout_20260417_v0.json",
        {"summary": {"decision": "RETAIN_REFINEMENT_v0", "authorized_follow_on": "NONE", "next_action": "STOP_PACKET01_FAMILY_AND_PRESERVE_REFINED_BASELINE", "packet01_family_closed": True}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json",
        {"summary": {"packet_decision": "INCONCLUSIVE_v0"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "direct_master_action_residual_transport_attack_class_packet_20260411_v0.json",
        {
            "summary": {
                "selected_target_row": "ROW-SEAM-QM-STAT-001",
                "selected_target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"
            },
            "single_bounded_target": {"seam_physics_blocker": "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"}
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "architecture_seam_master_action_alignment_packet_execution_20260411_v0.json",
        {"summary": {"execution_classification": "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "architecture_seam_master_action_alignment_ruling_20260411_v0.json",
        {"summary": {"alignment_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER"}},
    )
    _write_json(
        root / "formal" / "output" / "architecture" / "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json",
        {"row_id": "ROW-SEAM-QM-STAT-001", "status": "BOUND", "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"},
    )
    _write_json(
        root / "formal" / "output" / "architecture" / "MASTER_ACTION_RESIDUAL_EXTRACTION_BINDING_UNIT_v0.json",
        {"row_id": "ROW-SEAM-QM-STAT-001", "status": "MATERIALIZED", "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md",
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
        root / "formal" / "output" / "reports" / "seam_executable_path_normalization_20260418_v0.json",
        {
            "normalized_rows": [
                {
                    "seam_id": "SEAM-QM-STAT",
                    "path_class": "POLICY_BLOCKED_NONEXECUTABLE_PATH" if policy_blocked else "UNCLASSIFIED_PATH_STATE"
                }
            ]
        },
    )


def test_reports_recovery_state_materialized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "MASTER_ACTION_PACKET_01_TRANSPORT_BINDING_RECOVERY_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_STATE_MATERIALIZED"
    assert report["summary"]["transport_binding_blocker"] == "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"
    assert report["summary"]["canonical_transport_read_token"] == "PACKET01_PRESERVED_BASELINE_PLUS_WITNESS_BINDING_PLUS_MINIMAL_UPSTREAM_UNIT_PLUS_EXPLICIT_BLOCKER"


def test_reports_evidence_incomplete_when_qm_stat_path_not_policy_blocked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "MASTER_ACTION_PACKET_01_TRANSPORT_BINDING_RECOVERY_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, policy_blocked=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_EVIDENCE_INCOMPLETE"
