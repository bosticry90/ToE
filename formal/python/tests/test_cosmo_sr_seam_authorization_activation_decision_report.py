from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import cosmo_sr_seam_authorization_activation_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    tranche_overrides: dict | None = None,
    include_full_tranche_shape: bool = True,
) -> None:
    minimum_bounded_activation_tranche = {
        "target_row_id": "ROW-SEAM-COSMO-SR-001",
        "target_lane": "COSMO_SR_CYCLE07",
        "current_status": "NEXT_BOUNDED_DUAL_SEAM_CONTINUATION_EXECUTION_CHECKPOINT_PINNED",
        "required_evidence_surface": "formal/docs/paper/DERIVATION_TARGET_COSMO_SR_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE07_v0.md",
        "required_closure_artifact": "formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle07_v0.json",
        "required_closure_gate": "formal/python/tests/test_cosmo_sr_class_b_seam_physics_pilot_cycle07_gate.py",
        "required_exit_criterion": "CYCLE_GATE_AND_SYNTHESIS_GATE_PASS",
        "bounded_scope": "SINGLE_ROW_SINGLE_SEAM_COSMO_SR_CYCLE07_ACTIVATION_DECISION_ONLY",
    }
    if tranche_overrides:
        minimum_bounded_activation_tranche.update(tranche_overrides)
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
                "seam_resolution_sla_ledger_report": "formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json",
                "discovery_queue_transition_decision_report": "formal/output/reports/discovery_queue_transition_decision_report_20260411_v0.json",
                "discovery_queue_rescoring_pass_report": "formal/output/reports/discovery_queue_rescoring_pass_report_20260411_v0.json",
                "discovery_engine_review_checkpoint_report": "formal/output/reports/discovery_engine_review_checkpoint_20260411_v0.json",
                "discovery_engine_scoring_routing_review_report": "formal/output/reports/discovery_engine_scoring_routing_review_20260411_v0.json",
            },
            "authorization_activation_contract": {
                "required_tgc93_branch_decision": "AUTHORIZE_SINGLE_SEAM_REENTRY",
                "required_tgc93_seam_reentry_authorization": "AUTHORIZED",
                "required_transition_next_ranked_row": "ROW-SEAM-COSMO-SR-001",
                "required_transition_next_ranked_lane": "COSMO_SR_CYCLE07",
                "required_rescoring_rank3_candidate": "ROW-SEAM-COSMO-SR-001",
                "required_rescoring_terminal_route": "ACTIVATE_NEXT_RANKED_SEAM",
                "required_sla_decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION",
                "required_sla_gate_runtime_status": "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION",
                "hold_selected_expansion_decision": "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT",
                "hold_review_disposition": "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY",
                "authorized_selected_expansion_decision": "AUTHORIZE_ONE_NEW_DISCOVERY_SEAM_EXPANSION",
                "authorized_external_path_signal_present": True,
                "required_single_activation_cap": 1,
                "required_lane_expansion_reopen_condition": "CREDIBLE_EXTERNAL_PATH_SIGNAL_PRESENT_AND_RANK3_OVER_RANK4_GAP_GE_3_AND_DISCOVERY_REVIEW_HOLD_RESOLVED_ONCE",
                "single_layer_only": True,
                "single_outcome_only": True,
                "minimum_bounded_activation_tranche": minimum_bounded_activation_tranche,
            },
            "authorization_activation_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_OUTCOME",
                "no_loop_rule": "ONE_COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_LAYER_ONLY",
                "allowed_outcomes": [
                    "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_ACTIVATION_HELD",
                    "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_AUTHORIZED",
                    "COSMO_SR_AUTHORIZATION_ACTIVATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_COSMO_SR_AUTHORIZATION_ACTIVATION_REPAIR",
                ],
                "default_outcome": "COSMO_SR_AUTHORIZATION_ACTIVATION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    next_ranked_row_id: str = "ROW-SEAM-COSMO-SR-001",
    checkpoint_selected_expansion_decision: str = "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT",
    scoring_review_disposition: str = "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY",
    credible_external_path_signal_present: bool = False,
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
        root / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json",
        {
            "entries": [
                {
                    "row_id": "ROW-SEAM-COSMO-SR-001",
                    "lane": "COSMO_SR_CYCLE07",
                    "blocker_class": "SEAM_INTEGRATION_GAP",
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
    _write_json(
        root / "formal" / "output" / "reports" / "discovery_queue_transition_decision_report_20260411_v0.json",
        {
            "summary": {
                "selected_route": "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS",
                "next_ranked_row_id": next_ranked_row_id,
                "next_ranked_lane": "COSMO_SR_CYCLE07",
                "max_new_seam_activations_per_cycle": 1,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "discovery_queue_rescoring_pass_report_20260411_v0.json",
        {
            "summary": {
                "rank3_candidate": "ROW-SEAM-COSMO-SR-001",
                "terminal_route": "ACTIVATE_NEXT_RANKED_SEAM",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "discovery_engine_review_checkpoint_20260411_v0.json",
        {
            "summary": {
                "selected_expansion_decision": checkpoint_selected_expansion_decision,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "discovery_engine_scoring_routing_review_20260411_v0.json",
        {
            "summary": {
                "selected_review_disposition": scoring_review_disposition,
                "credible_external_path_signal_present": credible_external_path_signal_present,
                "lane_expansion_reopen_condition": "CREDIBLE_EXTERNAL_PATH_SIGNAL_PRESENT_AND_RANK3_OVER_RANK4_GAP_GE_3_AND_DISCOVERY_REVIEW_HOLD_RESOLVED_ONCE",
            }
        },
    )


def test_reports_cosmo_sr_single_active_candidate_activation_held(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_20260418_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_ACTIVATION_HELD"
    assert report["summary"]["activation_authorized_now"] is False
    assert report["summary"]["activation_hold_reason"] == "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT"


def test_reports_cosmo_sr_single_active_candidate_authorized_when_hold_clears(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_20260418_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        checkpoint_selected_expansion_decision="AUTHORIZE_ONE_NEW_DISCOVERY_SEAM_EXPANSION",
        scoring_review_disposition="CLEAR_TO_EXPAND",
        credible_external_path_signal_present=True,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_AUTHORIZED"
    assert report["summary"]["activation_authorized_now"] is True


def test_reports_cosmo_sr_activation_evidence_incomplete_when_candidate_changes(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_20260418_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, next_ranked_row_id="ROW-SEAM-QM-STAT-001")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "COSMO_SR_AUTHORIZATION_ACTIVATION_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_cosmo_sr_activation_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "COSMO_SR_SEAM_AUTHORIZATION_ACTIVATION_DECISION_20260418_v0.json"
    )
    _write_declaration(declaration_path, include_full_tranche_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_COSMO_SR_AUTHORIZATION_ACTIVATION_REPAIR"