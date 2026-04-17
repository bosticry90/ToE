from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_seam_authorization_readiness_dossier_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    tranche_overrides: dict | None = None,
    include_full_tranche_shape: bool = True,
) -> None:
    minimum_post_authorization_tranche = {
        "target_row_id": "ROW-SEAM-QM-STAT-001",
        "target_lane": "QM_STAT_CYCLE11",
        "current_status": "NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED",
        "required_evidence_surface": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
        "required_closure_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        "required_closure_gate": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
        "required_exit_criterion": "CYCLE_GATE_AND_SYNTHESIS_GATE_PASS",
        "bounded_scope": "SINGLE_ROW_SINGLE_SEAM_QM_STAT_CYCLE11_CONTINUATION_ONLY"
    }
    if tranche_overrides:
        minimum_post_authorization_tranche.update(tranche_overrides)
    if not include_full_tranche_shape:
        minimum_post_authorization_tranche.pop("required_exit_criterion")

    _write_json(
        path,
        {
            "target_seam": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "lane": "QM_STAT_CYCLE11",
                "blocker_class": "SEAM_INTEGRATION_GAP",
                "domain": "seam"
            },
            "required_inputs": {
                "discovery_priority_queue_report": "formal/output/reports/discovery_priority_queue_report_20260411_v0.json",
                "physics_progress_ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
                "bridge_external_validation_policy_standard_formalization_report": "formal/output/reports/bridge_external_validation_policy_standard_formalization_20260413_v0.json",
                "science_restart_higher_level_policy_trigger_report": "formal/output/reports/science_restart_higher_level_policy_trigger_20260413_v0.json",
                "science_restart_trigger_contract_report": "formal/output/reports/science_restart_trigger_contract_20260412_v0.json",
                "science_dormancy_preservation_audit_report": "formal/output/reports/science_dormancy_preservation_audit_20260412_v0.json"
            },
            "authorization_dossier_contract": {
                "required_discovery_queue_top_rank_row": "ROW-SEAM-QM-STAT-001",
                "required_progress_classification": "REWORK_ROUTED",
                "required_current_restart_blocker": "policy_standard_approval_not_recorded",
                "require_policy_standard_defined": True,
                "require_policy_standard_approved": False,
                "require_higher_level_policy_revision_authorized": False,
                "required_restart_terminal_outcome": "REMAIN_IN_GOVERNED_STOP_STATE",
                "required_dormancy_terminal_outcome": "DORMANCY_PRESERVATION_AUDIT_PASS",
                "required_direct_execution_authorized_now": False,
                "single_layer_only": True,
                "single_outcome_only": True,
                "minimum_post_authorization_tranche": minimum_post_authorization_tranche
            },
            "authorization_dossier_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_OUTCOME",
                "no_loop_rule": "ONE_QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_LAYER_ONLY",
                "allowed_outcomes": [
                    "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_BUT_RESTART_BLOCKED",
                    "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_QM_STAT_SEAM_AUTHORIZATION_DOSSIER_REPAIR"
                ],
                "default_outcome": "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(
    root: Path,
    *,
    top_rank_row: str = "ROW-SEAM-QM-STAT-001",
    include_restart_blocker: bool = True,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "discovery_priority_queue_report_20260411_v0.json",
        {
            "summary": {
                "top_rank_row": top_rank_row,
                "progress_classification": "REWORK_ROUTED"
            },
            "ranked_candidates": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "lane": "QM_STAT_CYCLE11",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
                    "required_closure_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                    "closure_gate": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
                    "score": 45
                }
            ]
        }
    )
    _write_json(
        root / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json",
        {
            "progress_classification": "REWORK_ROUTED",
            "evidence_bundle": {
                "closure_map": {
                    "row_level_evidence": [
                        {
                            "row_id": "ROW-SEAM-QM-STAT-001",
                            "blocker_class": "SEAM_INTEGRATION_GAP",
                            "required_closure_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                            "closure_gate": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
                            "exit_criterion": "CYCLE_GATE_AND_SYNTHESIS_GATE_PASS"
                        }
                    ]
                }
            }
        }
    )
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_standard_formalization_20260413_v0.json",
        {
            "criteria": {
                "policy_standard_defined": True,
                "policy_standard_approved": False
            },
            "summary": {
                "remaining_blockers_to_authorization": ["policy_standard_approval_not_recorded"]
                if include_restart_blocker
                else []
            }
        }
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_higher_level_policy_trigger_20260413_v0.json",
        {
            "summary": {
                "higher_level_policy_revision_authorized": False,
                "terminal_outcome": "HIGHER_LEVEL_POLICY_REVISION_NOT_AUTHORIZED"
            }
        }
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_trigger_contract_20260412_v0.json",
        {
            "summary": {
                "direct_execution_authorized_now": False,
                "terminal_outcome": "REMAIN_IN_GOVERNED_STOP_STATE"
            }
        }
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_dormancy_preservation_audit_20260412_v0.json",
        {
            "summary": {
                "direct_execution_authorized_now": False,
                "terminal_outcome": "DORMANCY_PRESERVATION_AUDIT_PASS"
            }
        }
    )


def test_reports_qm_stat_authorization_dossier_ready_but_restart_blocked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_20260414_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_BUT_RESTART_BLOCKED"
    assert report["summary"]["current_restart_blocker"] == "policy_standard_approval_not_recorded"
    assert report["summary"]["first_bounded_post_authorization_gate"] == (
        "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py"
    )


def test_reports_qm_stat_authorization_dossier_evidence_incomplete_when_top_rank_changes(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_20260414_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, top_rank_row="ROW-SEAM-QFT-GR-001")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_EVIDENCE_INCOMPLETE"


def test_reports_qm_stat_authorization_dossier_evidence_incomplete_when_restart_blocker_disappears(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_20260414_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, include_restart_blocker=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_qm_stat_authorization_dossier_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_20260414_v0.json"
    )
    _write_declaration(declaration_path, include_full_tranche_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_QM_STAT_SEAM_AUTHORIZATION_DOSSIER_REPAIR"