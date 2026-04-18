from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import post_plan_physics_advancement_target_map_report as tool


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
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "blocker_burn_dashboard_report": "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
                "seam_resolution_sla_ledger_report": "formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json",
                "seam_executable_path_normalization_report": "formal/output/reports/seam_executable_path_normalization_20260418_v0.json",
                "gr_row_001_blocker_file_map": "formal/docs/release/GR_ROW_001_NEW_STRUCTURE_BLOCKER_FILE_MAP_20260418_v0.json",
            },
            "target_map_policy": {
                "required_single_executable_row": "ROW-SEAM-COSMO-SR-001",
                "required_blocked_authority_row": "ROW-SEAM-QM-STAT-001",
                "required_external_hold_row": "ROW-SEAM-QFT-GR-001",
                "required_closed_monitoring_row": "ROW-SEAM-GR-QM-001",
                "required_gr_row_001": "ROW-PILLAR-GR-001",
                "required_gr_row_001_next_step": "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY",
                "required_progress_rule": "ONLY_LIVE_BLOCKER_OR_SEAM_STATE_MOVEMENT_COUNTS_AS_ADVANCEMENT",
                "theorem_gap_route_class": "THEOREM_GAP_PROGRAM",
                "frozen_new_structure_route_class": "FROZEN_NEW_STRUCTURE_BRANCH",
                "blocked_authority_route_class": "BLOCKED_PENDING_AUTHORITY",
                "external_hold_route_class": "EXTERNAL_HOLD",
                "closed_monitoring_route_class": "CLOSED_MONITORING",
                "executable_now_route_class": "EXECUTABLE_NOW",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED",
                    "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_REPAIR",
                ],
                "default_outcome": "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, cosmo_route_class: str = "SINGLE_AUTHORIZED_NONLIVE_EXECUTABLE_PATH") -> None:
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "\n".join(
            [
                "# Matrix",
                "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate | governance_checkpoint_status | physics_checkpoint_status | gate_runtime_status |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
                "| ROW-SEAM-QFT-GR-001 | seam | QFT_GR_REACTIVATION | SECOND_BOUNDED_INCREMENT_EXECUTION_CHECKPOINT_PINNED | SEAM_INTEGRATION_GAP | qft_target.md | qft.json | qft_gate.py | NOT_GOVERNANCE_COMPLETE | NOT_PHYSICS_COMPLETE | PATH_PINNED_RUNTIME_PENDING_BRANCH_EXCEPTION |",
                "| ROW-SEAM-QM-STAT-001 | seam | QM_STAT_CYCLE11 | NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED | SEAM_INTEGRATION_GAP | qm_target.md | qm.json | qm_gate.py | NOT_GOVERNANCE_COMPLETE | NOT_PHYSICS_COMPLETE | PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION |",
                "| ROW-SEAM-COSMO-SR-001 | seam | COSMO_SR_CYCLE07 | NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED | SEAM_INTEGRATION_GAP | cosmo_target.md | cosmo.json | cosmo_gate.py | NOT_GOVERNANCE_COMPLETE | NOT_PHYSICS_COMPLETE | PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION |",
                "| ROW-SEAM-GR-QM-001 | seam | GR_QM_PROMOTION | GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE | PARITY_DRIFT | gr_qm_target.md | gr_qm.lean | gr_qm_gate.py | GOVERNANCE_COMPLETE | PHYSICS_COMPLETE | GATE_RUNTIME_RECOMPUTE_MONITORING_REQUIRED |",
                "| ROW-PILLAR-GR-001 | pillar | GR_DERIVATION_CHAIN | SECOND_BOUNDED_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | gr_target.md | gr.json | gr_gate.py | NOT_APPLICABLE_PILLAR_ROW | THEOREM_GAP_OPEN | PATH_PINNED_RUNTIME_RECORDED |",
                "| ROW-PILLAR-QM-001 | pillar | QM_DERIVATION_CHAIN | THEOREM_GAP_CLOSURE_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | qm_pillar_target.md | qm_pillar.json | qm_pillar_gate.py | NOT_APPLICABLE_PILLAR_ROW | THEOREM_GAP_OPEN | PATH_PINNED_RUNTIME_RECORDED |",
            ]
        ),
    )
    _write_json(
        root / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json",
        {
            "blocker_scoreboard": {"movement_status": "DECREASING", "net_delta": -1},
            "closure_map_linkage": {
                "mapped_rows": [
                    {"row_id": "ROW-SEAM-QFT-GR-001", "closure_gate": "qft_gate.py", "exit_criterion": "gate"},
                    {"row_id": "ROW-SEAM-QM-STAT-001", "closure_gate": "qm_gate.py", "exit_criterion": "gate"},
                    {"row_id": "ROW-SEAM-COSMO-SR-001", "closure_gate": "cosmo_gate.py", "exit_criterion": "gate"},
                    {"row_id": "ROW-SEAM-GR-QM-001", "closure_gate": "gr_qm_gate.py", "exit_criterion": "gate"},
                    {"row_id": "ROW-PILLAR-GR-001", "closure_gate": "gr_gate.py", "exit_criterion": "gate"},
                    {"row_id": "ROW-PILLAR-QM-001", "closure_gate": "qm_pillar_gate.py", "exit_criterion": "gate"},
                ]
            },
            "row_promotion_readiness": {
                "rows": [
                    {"row_id": "ROW-SEAM-QFT-GR-001", "promotion_readiness_status": "READY", "gate_runtime_status": "PATH_PINNED_RUNTIME_PENDING_BRANCH_EXCEPTION"},
                    {"row_id": "ROW-SEAM-QM-STAT-001", "promotion_readiness_status": "READY", "gate_runtime_status": "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION"},
                    {"row_id": "ROW-SEAM-COSMO-SR-001", "promotion_readiness_status": "READY", "gate_runtime_status": "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION"},
                    {"row_id": "ROW-SEAM-GR-QM-001", "promotion_readiness_status": "READY", "gate_runtime_status": "GATE_RUNTIME_RECOMPUTE_MONITORING_REQUIRED"},
                    {"row_id": "ROW-PILLAR-GR-001", "promotion_readiness_status": "READY", "gate_runtime_status": "PATH_PINNED_RUNTIME_RECORDED"},
                    {"row_id": "ROW-PILLAR-QM-001", "promotion_readiness_status": "READY", "gate_runtime_status": "PATH_PINNED_RUNTIME_RECORDED"},
                ]
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json",
        {
            "dashboard_coupling": {"movement_status": "FLAT", "stale_input_warning": True},
            "entries": [
                {"row_id": "ROW-SEAM-QFT-GR-001", "seam_id": "SEAM-QFT-GR", "decision_state": "HOLD_RETAINED_EXTERNAL_HOLD_RELEASE_REQUIRED"},
                {"row_id": "ROW-SEAM-QM-STAT-001", "seam_id": "SEAM-QM-STAT", "decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION"},
                {"row_id": "ROW-SEAM-COSMO-SR-001", "seam_id": "SEAM-COSMO-SR", "decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION"},
                {"row_id": "ROW-SEAM-GR-QM-001", "seam_id": "SEAM-GR-QM", "decision_state": "CLOSED_RECOMPUTE_MONITORING_REQUIRED"},
            ],
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "seam_executable_path_normalization_20260418_v0.json",
        {
            "normalized_rows": [
                {"seam_id": "SEAM-QFT-GR", "path_class": "EXTERNAL_HOLD_NONEXECUTABLE_PATH", "next_action": "WAIT_FOR_SCALAR_PUBLICATION_RELEASE_ONLY"},
                {"seam_id": "SEAM-QM-STAT", "path_class": "POLICY_BLOCKED_NONEXECUTABLE_PATH", "next_action": "RECORD_POLICY_STANDARD_APPROVAL_BEFORE_ANY_QM_STAT_RESTART_AUTHORIZATION"},
                {"seam_id": "SEAM-COSMO-SR", "path_class": cosmo_route_class, "next_action": "EXECUTE_ONE_BOUNDED_COSMO_SR_CYCLE07_ACTIVATION_ONLY"},
                {"seam_id": "SEAM-GR-QM", "path_class": "CLOSED_MONITORING_NONEXECUTABLE_PATH", "next_action": "REMAIN_IN_RECOMPUTE_MONITORING_ONLY"},
            ]
        },
    )
    _write_json(
        root / "formal" / "docs" / "release" / "GR_ROW_001_NEW_STRUCTURE_BLOCKER_FILE_MAP_20260418_v0.json",
        {
            "target_row": "ROW-PILLAR-GR-001",
            "authoritative_branch_classification": {
                "current_lane_class": "FROZEN_NEW_STRUCTURE_BRANCH",
                "authoritative_next_step": "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY",
                "authoritative_next_action": "KEEP_GR_ROW_001_FROZEN_AND_PREPARE_ONE_BOUNDED_SHARED_INTERFACE_DECLARATION_IF_RESTART_AUTHORIZED",
            },
        },
    )


def test_reports_target_map_materialized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"
    route_map = {row["row_id"]: row for row in report["routed_rows"]}
    assert route_map["ROW-SEAM-COSMO-SR-001"]["route_class"] == "EXECUTABLE_NOW"
    assert route_map["ROW-SEAM-QM-STAT-001"]["route_class"] == "BLOCKED_PENDING_AUTHORITY"
    assert route_map["ROW-SEAM-QFT-GR-001"]["route_class"] == "EXTERNAL_HOLD"
    assert route_map["ROW-SEAM-GR-QM-001"]["route_class"] == "CLOSED_MONITORING"
    assert route_map["ROW-PILLAR-GR-001"]["route_class"] == "FROZEN_NEW_STRUCTURE_BRANCH"
    assert route_map["ROW-PILLAR-GR-001"]["authoritative_next_step"] == "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY"
    assert route_map["ROW-PILLAR-QM-001"]["route_class"] == "THEOREM_GAP_PROGRAM"


def test_reports_evidence_incomplete_when_no_single_executable_seam(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, cosmo_route_class="POLICY_BLOCKED_NONEXECUTABLE_PATH")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_EVIDENCE_INCOMPLETE"