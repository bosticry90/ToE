from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import cosmo_sr_discovery_review_hold_resolution_report as tool


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
            "target_seam": {
                "row_id": "ROW-SEAM-COSMO-SR-001",
                "lane": "COSMO_SR_CYCLE07",
                "blocker_class": "SEAM_INTEGRATION_GAP",
                "domain": "seam",
            },
            "required_inputs": {
                "tgc93_branch_decision_package": "formal/docs/release/WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md",
                "cosmo_sr_seam_authorization_activation_decision_report": "formal/output/reports/cosmo_sr_seam_authorization_activation_decision_20260418_v0.json",
                "discovery_queue_transition_decision_report": "formal/output/reports/discovery_queue_transition_decision_report_20260411_v0.json",
                "discovery_engine_review_checkpoint_report": "formal/output/reports/discovery_engine_review_checkpoint_20260411_v0.json",
                "discovery_engine_scoring_routing_review_report": "formal/output/reports/discovery_engine_scoring_routing_review_20260411_v0.json",
            },
            "hold_resolution_contract": {
                "required_tgc93_branch_decision": "AUTHORIZE_SINGLE_SEAM_REENTRY",
                "required_tgc93_seam_reentry_authorization": "AUTHORIZED",
                "required_phase2_decision_outcome": "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_ACTIVATION_HELD",
                "required_transition_next_ranked_row": "ROW-SEAM-COSMO-SR-001",
                "required_transition_next_ranked_lane": "COSMO_SR_CYCLE07",
                "required_single_activation_cap": 1,
                "required_checkpoint_hold_decision": "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT",
                "required_scoring_review_disposition": "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY",
                "required_credible_external_path_signal_present": False,
                "hold_scope_rule": "NO_FURTHER_LANE_EXPANSION_UNTIL_REVIEW_CHECKPOINT_RESOLVED",
                "hold_scope_interpretation": "CHECKPOINT_HOLD_GOVERNS_FURTHER_DISCOVERY_EXPANSION_NOT_CONVERSION_OF_THE_ALREADY_SELECTED_SINGLE_NONFROZEN_TGC93_CANDIDATE",
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "hold_resolution_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_OUTCOME",
                "no_loop_rule": "ONE_COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_LAYER_ONLY",
                "allowed_outcomes": [
                    "COSMO_SR_SINGLE_CANDIDATE_HOLD_RESOLVED_FOR_AUTHORIZATION_CONVERSION",
                    "COSMO_SR_DISCOVERY_REVIEW_HOLD_REMAINS_ACTIVE",
                    "COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_REPAIR",
                ],
                "default_outcome": "COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase2_outcome: str = "COSMO_SR_SINGLE_ACTIVE_CANDIDATE_ACTIVATION_HELD",
    checkpoint_hold_policy: str = "NO_FURTHER_LANE_EXPANSION_UNTIL_REVIEW_CHECKPOINT_RESOLVED",
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
                "terminal_outcome": phase2_outcome,
                "target_row_id": "ROW-SEAM-COSMO-SR-001",
                "target_lane": "COSMO_SR_CYCLE07",
                "single_non_frozen_candidate_confirmed": True,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "discovery_queue_transition_decision_report_20260411_v0.json",
        {
            "summary": {
                "next_ranked_row_id": "ROW-SEAM-COSMO-SR-001",
                "next_ranked_lane": "COSMO_SR_CYCLE07",
                "max_new_seam_activations_per_cycle": 1,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "discovery_engine_review_checkpoint_20260411_v0.json",
        {
            "summary": {
                "selected_expansion_decision": "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT",
                "hold_policy": checkpoint_hold_policy,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "discovery_engine_scoring_routing_review_20260411_v0.json",
        {
            "summary": {
                "selected_review_disposition": "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY",
                "credible_external_path_signal_present": False,
            }
        },
    )


def test_reports_hold_resolved_for_authorization_conversion(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "COSMO_SR_SINGLE_CANDIDATE_HOLD_RESOLVED_FOR_AUTHORIZATION_CONVERSION"


def test_reports_hold_remains_when_scope_rule_is_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "COSMO_SR_DISCOVERY_REVIEW_HOLD_RESOLUTION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, checkpoint_hold_policy="HOLD_POLICY_TEXT_MISSING_SCOPE_RULE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "COSMO_SR_DISCOVERY_REVIEW_HOLD_REMAINS_ACTIVE"
