from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import discovery_engine_review_checkpoint_report as checkpoint_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "current_mode": "CONTROL_PLUS_DISCOVERY_OVERLAY",
            "required_inputs": {
                "discovery_engine_transition_packet": "formal/docs/release/DISCOVERY_ENGINE_TRANSITION_PACKET_20260411_v0.json",
                "discovery_queue_transition_decision_report": "formal/output/reports/discovery_queue_transition_decision_report_20260411_v0.json",
                "discovery_queue_review_pass_report": "formal/output/reports/discovery_queue_review_pass_report_20260411_v0.json",
                "discovery_queue_rescoring_pass_report": "formal/output/reports/discovery_queue_rescoring_pass_report_20260411_v0.json",
                "qm_stat_discovery_ruling_report": "formal/output/reports/qm_stat_discovery_ruling_report_20260411_v0.json",
                "qm_stat_post_cycle_decision_report": "formal/output/reports/qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
                "qft_gr_discovery_ruling_report": "formal/output/reports/qft_gr_discovery_ruling_report_20260411_v0.json",
                "qft_gr_post_cycle_decision_report": "formal/output/reports/qft_gr_discovery_post_cycle_decision_report_20260411_v0.json",
                "gr_discovery_discriminator_tranche_report": "formal/output/reports/gr_discovery_discriminator_tranche_report_20260411_v0.json",
                "gr_discovery_ruling_report": "formal/output/reports/gr_discovery_ruling_report_20260411_v0.json",
            },
            "review_questions": [
                "IS_DISCOVERY_YIELD_IMPROVING_RELATIVE_TO_PRETRANSITION_BASELINE",
                "ARE_INTERNAL_ONLY_DISCRIMINATOR_SEAMS_ACCUMULATING_TOWARD_A_STRONGER_EXTERNAL_PATH",
                "SHOULD_NEXT_EXPANSION_OPEN_ANOTHER_SEAM_OR_REASSESS_SCORING_ROUTING_FIRST",
            ],
            "decision_policy": {
                "pretransition_baseline_inference_rule": "MODE_TRANSITION_FROM_CONTROL_MODE_PRIMARY_IMPLIES_ZERO_DISCOVERY_OVERLAY_BASELINE",
                "minimum_internal_only_lanes_for_review_hold": 2,
                "pause_when_yield_improves_but_external_path_not_established": True,
                "allow_expansion_only_when_external_discriminative_leverage_established": True,
                "hold_policy": "NO_FURTHER_LANE_EXPANSION_UNTIL_REVIEW_CHECKPOINT_RESOLVED",
                "pause_next_action": "REASSESS_DISCOVERY_SCORING_ROUTING_BEFORE_ANY_FURTHER_LANE_EXPANSION",
                "expansion_next_action": "AUTHORIZE_ONE_NEW_DISCOVERY_SEAM_EXPANSION",
                "repair_next_action": "RESTORE_DISCOVERY_REVIEW_INPUTS_AND_REEVALUATE_ONCE",
            },
        },
    )


def _write_common_inputs(reports_dir: Path, release_dir: Path) -> None:
    _write_json(
        release_dir / "DISCOVERY_ENGINE_TRANSITION_PACKET_20260411_v0.json",
        {
            "mode_transition": {
                "from": "CONTROL_MODE_PRIMARY",
                "to": "CONTROL_PLUS_DISCOVERY_OVERLAY",
            },
            "primary_optimization_target": {"metric_name": "DISCOVERY_YIELD"},
        },
    )
    _write_json(
        reports_dir / "discovery_queue_transition_decision_report_20260411_v0.json",
        {"summary": {"selected_route": "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS", "external_discriminative_leverage_established": False}},
    )
    _write_json(
        reports_dir / "discovery_queue_review_pass_report_20260411_v0.json",
        {"summary": {"selected_next_route": "EXECUTE_ONE_BOUNDED_QUEUE_RESCORING"}},
    )
    _write_json(
        reports_dir / "discovery_queue_rescoring_pass_report_20260411_v0.json",
        {"summary": {"terminal_route": "ACTIVATE_NEXT_RANKED_SEAM", "rank_gap_after_rescoring": 3}},
    )
    _write_json(
        reports_dir / "qm_stat_discovery_ruling_report_20260411_v0.json",
        {"summary": {"ruling": "DISCRIMINATOR_PRODUCED", "ruling_status": "TERMINAL_OUTCOME_CONFIRMED"}},
    )
    _write_json(
        reports_dir / "qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
        {"summary": {"interpretation": "INTERNAL_DISCRIMINATIVE_ONLY"}},
    )
    _write_json(
        reports_dir / "qft_gr_discovery_ruling_report_20260411_v0.json",
        {"summary": {"ruling": "DISCRIMINATOR_PRODUCED", "ruling_status": "TERMINAL_OUTCOME_CONFIRMED"}},
    )
    _write_json(
        reports_dir / "qft_gr_discovery_post_cycle_decision_report_20260411_v0.json",
        {"summary": {"interpretation": "INTERNAL_DISCRIMINATIVE_ONLY"}},
    )
    _write_json(
        reports_dir / "gr_discovery_discriminator_tranche_report_20260411_v0.json",
        {"summary": {"execution_classification": "DISCOVERY_TRANCHE_EXECUTABLE", "target_row": "ROW-PILLAR-GR-001"}},
    )
    _write_json(
        reports_dir / "gr_discovery_ruling_report_20260411_v0.json",
        {"summary": {"ruling_status": "TERMINAL_OUTCOME_CONFIRMED", "ruling": "DISCRIMINATOR_PRODUCED"}},
    )


def test_discovery_review_checkpoint_pauses_before_further_lane_expansion(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(checkpoint_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_REVIEW_CHECKPOINT_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"
    release_dir = tmp_path / "formal" / "docs" / "release"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir, release_dir)

    report = checkpoint_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["discovery_yield_relative_to_pretransition_baseline"] == "IMPROVED_FROM_ZERO_PRETRANSITION_BASELINE"
    assert report["summary"]["internal_only_discriminator_accumulation_status"] == "INTERNAL_ONLY_SEAMS_ACCUMULATING_WITHOUT_EXTERNAL_PATH"
    assert report["summary"]["selected_expansion_decision"] == "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT"
    assert report["summary"]["next_action"] == "REASSESS_DISCOVERY_SCORING_ROUTING_BEFORE_ANY_FURTHER_LANE_EXPANSION"


def test_discovery_review_checkpoint_allows_one_expansion_when_external_path_is_established(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(checkpoint_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_REVIEW_CHECKPOINT_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"
    release_dir = tmp_path / "formal" / "docs" / "release"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir, release_dir)
    _write_json(
        reports_dir / "discovery_queue_transition_decision_report_20260411_v0.json",
        {"summary": {"selected_route": "EXECUTE_BOUNDED_QUEUE_REVIEW_PASS", "external_discriminative_leverage_established": True}},
    )

    report = checkpoint_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["selected_expansion_decision"] == "ALLOW_ONE_NEW_DISCOVERY_SEAM_EXPANSION"
    assert report["summary"]["next_action"] == "AUTHORIZE_ONE_NEW_DISCOVERY_SEAM_EXPANSION"


def test_discovery_review_checkpoint_requires_repair_when_gr_shadow_state_is_missing(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(checkpoint_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_REVIEW_CHECKPOINT_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"
    release_dir = tmp_path / "formal" / "docs" / "release"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir, release_dir)
    _write_json(
        reports_dir / "gr_discovery_ruling_report_20260411_v0.json",
        {"summary": {"ruling_status": "TERMINAL_OUTCOME_BLOCKED", "ruling": "NONPRODUCTIVE_RETIRED"}},
    )

    report = checkpoint_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["selected_expansion_decision"] == "CHECKPOINT_INPUT_REPAIR_REQUIRED_OR_REASSESSMENT_INCOMPLETE"
    assert report["summary"]["next_action"] == "RESTORE_DISCOVERY_REVIEW_INPUTS_AND_REEVALUATE_ONCE"
