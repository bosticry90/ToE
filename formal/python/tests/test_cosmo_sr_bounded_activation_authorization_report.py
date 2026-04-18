from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import cosmo_sr_bounded_activation_authorization_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_tranche_shape: bool = True) -> None:
    minimum_bounded_activation_tranche = {
        "target_row_id": "ROW-SEAM-COSMO-SR-001",
        "target_lane": "COSMO_SR_CYCLE07",
        "current_status": "NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED",
        "required_evidence_surface": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md",
        "required_closure_artifact": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
        "required_closure_gate": "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py",
        "required_exit_criterion": "CYCLE_GATE_AND_SYNTHESIS_GATE_PASS",
        "bounded_scope": "SINGLE_ROW_SINGLE_SEAM_COSMO_SR_CYCLE07_ACTIVATION_AUTHORIZATION_ONLY",
    }
    if not include_full_tranche_shape:
        minimum_bounded_activation_tranche.pop("required_exit_criterion")

    _write_json(
        path,
        {
            "target_seam": {
                "row_id": "ROW-SEAM-COSMO-SR-001",
                "lane": "COSMO_SR_CYCLE07",
                "blocker_class": "SEAM_INTEGRATION_GAP",
                "domain": "seam",
            },
            "required_inputs": {
                "tgc93_branch_decision_package": "formal/docs/release/WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md",
                "cosmo_sr_seam_authorization_activation_decision_report": "formal/output/reports/cosmo_sr_seam_authorization_activation_decision_20260418_v0.json",
                "cosmo_sr_discovery_review_hold_resolution_report": "formal/output/reports/cosmo_sr_discovery_review_hold_resolution_20260418_v0.json",
                "seam_resolution_sla_ledger_report": "formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json",
            },
            "bounded_activation_authorization_contract": {
                "required_tgc93_branch_decision": "AUTHORIZE_SINGLE_SEAM_REENTRY",
                "required_tgc93_seam_reentry_authorization": "AUTHORIZED",
                "required_phase2_decision_outcome": "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_ACTIVATION_HELD",
                "required_hold_resolution_outcome": "COSMO_SR_SINGLE_CANDIDATE_HOLD_RESOLVED_FOR_AUTHORIZATION_CONVERSION",
                "required_sla_decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION",
                "required_sla_gate_runtime_status": "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION",
                "authorization_scope_token": "CONTROL_SURFACE_COSMO_SR_CYCLE07_BOUNDED_ACTIVATION_AUTHORIZATION_NONLIVE",
                "authorization_result_token": "COSMO_SR_CYCLE07_SINGLE_LANE_ACTIVATION_AUTHORIZED_NONLIVE_v0",
                "branch_chain_status": "UNAMBIGUOUS_SINGLE_ACTIVE_SEAM_PATH",
                "execution_live_token_count": 0,
                "single_layer_only": True,
                "single_outcome_only": True,
                "minimum_bounded_activation_tranche": minimum_bounded_activation_tranche,
            },
            "bounded_activation_authorization_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_OUTCOME",
                "no_loop_rule": "ONE_COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "COSMO_SR_CYCLE07_SINGLE_LANE_ACTIVATION_AUTHORIZED_NONLIVE_v0",
                    "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_BLOCKED",
                    "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_REPAIR",
                ],
                "default_outcome": "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    hold_resolution_outcome: str = "COSMO_SR_SINGLE_CANDIDATE_HOLD_RESOLVED_FOR_AUTHORIZATION_CONVERSION",
) -> None:
    _write_text(
        root / "formal" / "docs" / "release" / "WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md",
        "\n".join(
            [
                "# WS-10 TGC-93 Branch Decision Package",
                "- `TGC93_BRANCH_DECISION_v0: AUTHORIZE_SINGLE_SEAM_REENTRY`",
                "- `TGC93_SEAM_REENTRY_AUTHORIZATION_v0: AUTHORIZED`",
            ]
        ),
    )
    _write_json(
        root / "formal" / "output" / "reports" / "cosmo_sr_seam_authorization_activation_decision_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_ACTIVATION_HELD",
                "target_row_id": "ROW-SEAM-COSMO-SR-001",
                "target_lane": "COSMO_SR_CYCLE07",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "cosmo_sr_discovery_review_hold_resolution_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": hold_resolution_outcome,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json",
        {
            "entries": [
                {
                    "row_id": "ROW-SEAM-COSMO-SR-001",
                    "decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION",
                    "gate_runtime_status": "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION",
                    "target_surface": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md",
                    "artifact_surface": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
                    "gate_surface": "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py",
                    "exit_criterion": "CYCLE_GATE_AND_SYNTHESIS_GATE_PASS",
                }
            ]
        },
    )


def test_reports_cosmo_sr_bounded_activation_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "COSMO_SR_CYCLE07_SINGLE_LANE_ACTIVATION_AUTHORIZED_NONLIVE_v0"
    assert report["summary"]["authorization_scope_token"] == "CONTROL_SURFACE_COSMO_SR_CYCLE07_BOUNDED_ACTIVATION_AUTHORIZATION_NONLIVE"


def test_reports_cosmo_sr_bounded_activation_blocked_when_hold_resolution_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, hold_resolution_outcome="COSMO_SR_DISCOVERY_REVIEW_HOLD_REMAINS_ACTIVE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_BLOCKED"
