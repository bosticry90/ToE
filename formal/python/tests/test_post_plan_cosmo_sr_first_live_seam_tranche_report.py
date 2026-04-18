from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import post_plan_cosmo_sr_first_live_seam_tranche_report as tool


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
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "cosmo_sr_bounded_activation_authorization_report": "formal/output/reports/cosmo_sr_bounded_activation_authorization_20260418_v0.json",
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "blocker_burn_dashboard_report": "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
                "cosmo_sr_target_doc": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md",
                "cosmo_sr_cycle07_artifact": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
                "cosmo_sr_cycle07_gate": "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py",
            },
            "execution_policy": {
                "required_target_row": "ROW-SEAM-COSMO-SR-001",
                "required_target_seam": "SEAM-COSMO-SR",
                "required_target_route_class": "EXECUTABLE_NOW",
                "required_authorization_outcome": "COSMO_SR_CYCLE07_SINGLE_LANE_ACTIVATION_AUTHORIZED_NONLIVE_v0",
                "required_authorization_next_action": "EXECUTE_ONE_BOUNDED_COSMO_SR_CYCLE07_ACTIVATION_ONLY",
                "required_artifact_adjudication": "NOT_YET_DISCHARGED",
                "required_row_blocker_class": "SEAM_INTEGRATION_GAP",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_COSMO_SR_TRANCHE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_COSMO_SR_TRANCHE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_NONPROMOTED",
                    "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_AND_PROMOTED",
                    "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_COSMO_SR_TRANCHE_REPAIR",
                ],
                "default_outcome": "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, promoted: bool = False) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED",
                "executable_now_rows": ["ROW-SEAM-COSMO-SR-001"],
            },
            "routed_rows": [
                {
                    "row_id": "ROW-SEAM-COSMO-SR-001",
                    "route_class": "EXECUTABLE_NOW",
                    "authoritative_next_action": "EXECUTE_ONE_BOUNDED_COSMO_SR_CYCLE07_ACTIVATION_ONLY",
                }
            ],
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "cosmo_sr_bounded_activation_authorization_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "COSMO_SR_CYCLE07_SINGLE_LANE_ACTIVATION_AUTHORIZED_NONLIVE_v0",
                "next_action": "EXECUTE_ONE_BOUNDED_COSMO_SR_CYCLE07_ACTIVATION_ONLY",
                "target_row_id": "ROW-SEAM-COSMO-SR-001",
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "\n".join(
            [
                "# Matrix",
                "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate | governance_checkpoint_status | physics_checkpoint_status | gate_runtime_status |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
                f"| ROW-SEAM-COSMO-SR-001 | seam | COSMO_SR_CYCLE07 | {'GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE' if promoted else 'NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED'} | SEAM_INTEGRATION_GAP | formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md | formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json | formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py | {'GOVERNANCE_COMPLETE' if promoted else 'NOT_GOVERNANCE_COMPLETE'} | {'PHYSICS_COMPLETE' if promoted else 'NOT_PHYSICS_COMPLETE'} | PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION |",
            ]
        ),
    )
    _write_json(
        root / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json",
        {"blocker_scoreboard": {"movement_status": "DECREASING", "net_delta": -1}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md",
        "\n".join(
            [
                "DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0",
                "COSMO_SR_CYCLE07_STATUS_v0: DODECIC_LOW_Z_ALIGNMENT_AND_EXCLUSION_PINNED_NONCLAIM",
                "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
                "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py",
            ]
        ),
    )
    _write_json(
        root / "formal" / "output" / "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
        {
            "artifact_id": "cosmo_sr_class_b_seam_physics_pilot_cycle07_v0",
            "seam_id": "SEAM-COSMO-SR",
            "adjudication": {"value": "DISCHARGED" if promoted else "NOT_YET_DISCHARGED"},
        },
    )
    _write_text(
        root / "formal" / "python" / "tests" / "test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py",
        "def test_gate_exists():\n    assert True\n",
    )


def test_reports_nonpromoted_tranche_when_row_truth_unchanged(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, promoted=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_NONPROMOTED"
    assert report["summary"]["row_truth_change_detected"] is False


def test_reports_promoted_tranche_when_row_truth_changes(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, promoted=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_AND_PROMOTED"
    assert report["summary"]["row_truth_change_detected"] is True