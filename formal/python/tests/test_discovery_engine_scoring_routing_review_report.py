from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import discovery_engine_scoring_routing_review_report as review_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "discovery_priority_queue_declaration": "formal/docs/release/DISCOVERY_PRIORITY_QUEUE_20260411_v0.json",
                "discovery_priority_queue_report": "formal/output/reports/discovery_priority_queue_report_20260411_v0.json",
                "discovery_queue_transition_declaration": "formal/docs/release/DISCOVERY_QUEUE_TRANSITION_DECISION_20260411_v0.json",
                "discovery_queue_transition_decision_report": "formal/output/reports/discovery_queue_transition_decision_report_20260411_v0.json",
                "discovery_queue_review_pass_report": "formal/output/reports/discovery_queue_review_pass_report_20260411_v0.json",
                "discovery_queue_rescoring_pass_report": "formal/output/reports/discovery_queue_rescoring_pass_report_20260411_v0.json",
                "discovery_engine_review_checkpoint_report": "formal/output/reports/discovery_engine_review_checkpoint_20260411_v0.json",
                "qm_stat_discovery_interpretation_report": "formal/output/reports/qm_stat_discovery_interpretation_report_20260411_v0.json",
                "qft_gr_discovery_interpretation_report": "formal/output/reports/qft_gr_discovery_interpretation_report_20260411_v0.json",
            },
            "review_questions": [
                "REASSESS_DISCOVERY_SCORING_WEIGHTS",
                "REASSESS_DISCOVERY_ROUTING_THRESHOLDS",
                "DEFINE_CREDIBLE_EXTERNAL_PATH_SIGNAL",
                "DEFINE_EXACT_LANE_EXPANSION_REOPEN_CONDITION",
            ],
            "review_policy": {
                "retain_base_score_formula_when_queue_behavior_is_coherent": True,
                "require_external_path_signal_for_lane_expansion_reopen": True,
                "rank_gap_threshold_for_reopen": 3,
                "hold_when_internal_only_accumulation_persists_without_external_path": True,
                "default_hold_next_action": "MAINTAIN_DISCOVERY_HOLD_AND_REASSESS_SCORING_ROUTING_RULES_ONLY",
                "default_reopen_next_action": "AUTHORIZE_ONE_BOUNDED_LANE_EXPANSION",
                "default_repair_next_action": "RESTORE_REVIEW_INPUTS_AND_REEVALUATE_DISCOVERY_SCORING_ROUTING_ONCE",
            },
        },
    )


def _write_common_inputs(reports_dir: Path, release_dir: Path) -> None:
    _write_json(
        release_dir / "DISCOVERY_PRIORITY_QUEUE_20260411_v0.json",
        {"ranking_policy": {"score_formula": "4x_D+3x_F+2x_B+1x_E"}},
    )
    _write_json(
        release_dir / "DISCOVERY_QUEUE_TRANSITION_DECISION_20260411_v0.json",
        {"decision_policy": {"min_rank3_score_gap_over_rank4_for_activation": 3}},
    )
    _write_json(reports_dir / "discovery_priority_queue_report_20260411_v0.json", {"summary": {"top_rank_row": "ROW-SEAM-QM-STAT-001"}})
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
        reports_dir / "discovery_engine_review_checkpoint_20260411_v0.json",
        {
            "summary": {
                "selected_expansion_decision": "PAUSE_FOR_DISCOVERY_ENGINE_REVIEW_CHECKPOINT",
                "internal_only_discriminator_accumulation_status": "INTERNAL_ONLY_SEAMS_ACCUMULATING_WITHOUT_EXTERNAL_PATH",
            },
            "objective_quality": {
                "inputs": {
                    "queue_state": {"external_discriminative_leverage_established": False},
                }
            },
        },
    )
    _write_json(
        reports_dir / "qm_stat_discovery_interpretation_report_20260411_v0.json",
        {
            "summary": {
                "interpretation": "INTERNAL_DISCRIMINATIVE_ONLY",
                "externally_comparable": False,
                "numerical_probe_ready": False,
            }
        },
    )
    _write_json(
        reports_dir / "qft_gr_discovery_interpretation_report_20260411_v0.json",
        {
            "summary": {
                "interpretation": "INTERNAL_DISCRIMINATIVE_ONLY",
                "probe_ready": False,
                "probe_lane_allowed": False,
            }
        },
    )


def test_scoring_routing_review_holds_when_queue_is_coherent_but_external_path_absent(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_SCORING_ROUTING_REVIEW_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"
    release_dir = tmp_path / "formal" / "docs" / "release"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir, release_dir)

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["scoring_weight_assessment"] == "KEEP_BASE_WEIGHTS_ADD_EXTERNAL_PATH_GATING_OVERLAY"
    assert report["summary"]["routing_threshold_assessment"] == "RANK_GAP_THRESHOLD_3_REMAINS_NECESSARY_BUT_NOT_SUFFICIENT_WITHOUT_EXTERNAL_PATH_SIGNAL"
    assert report["summary"]["credible_external_path_signal_present"] is False
    assert report["summary"]["selected_review_disposition"] == "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY"


def test_scoring_routing_review_reopens_when_external_path_signal_is_present(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_SCORING_ROUTING_REVIEW_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"
    release_dir = tmp_path / "formal" / "docs" / "release"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir, release_dir)
    _write_json(
        reports_dir / "discovery_engine_review_checkpoint_20260411_v0.json",
        {
            "summary": {
                "selected_expansion_decision": "ALLOW_ONE_NEW_DISCOVERY_SEAM_EXPANSION",
                "internal_only_discriminator_accumulation_status": "INTERNAL_ONLY_SEAMS_ACCUMULATING_TOWARD_EXTERNAL_PATH",
            },
            "objective_quality": {
                "inputs": {
                    "queue_state": {"external_discriminative_leverage_established": True},
                }
            },
        },
    )
    _write_json(
        reports_dir / "qm_stat_discovery_interpretation_report_20260411_v0.json",
        {
            "summary": {
                "interpretation": "NUMERICAL_PROBE_READY",
                "externally_comparable": True,
                "numerical_probe_ready": True,
            }
        },
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["credible_external_path_signal_present"] is True
    assert report["summary"]["selected_review_disposition"] == "REOPEN_ONE_BOUNDED_LANE_EXPANSION"
    assert report["summary"]["next_action"] == "AUTHORIZE_ONE_BOUNDED_LANE_EXPANSION"


def test_scoring_routing_review_keeps_queue_coherent_when_rescored_gap_exceeds_threshold(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_SCORING_ROUTING_REVIEW_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"
    release_dir = tmp_path / "formal" / "docs" / "release"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir, release_dir)
    _write_json(
        reports_dir / "discovery_queue_rescoring_pass_report_20260411_v0.json",
        {"summary": {"terminal_route": "ACTIVATE_NEXT_RANKED_SEAM", "rank_gap_after_rescoring": 4}},
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["scoring_weight_assessment"] == "KEEP_BASE_WEIGHTS_ADD_EXTERNAL_PATH_GATING_OVERLAY"
    assert report["summary"]["selected_review_disposition"] == "HOLD_EXPANSION_REASSESS_SCORING_ROUTING_ONLY"


def test_scoring_routing_review_requires_repair_when_queue_behavior_is_not_coherent(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "DISCOVERY_ENGINE_SCORING_ROUTING_REVIEW_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"
    release_dir = tmp_path / "formal" / "docs" / "release"

    _write_declaration(declaration_path)
    _write_common_inputs(reports_dir, release_dir)
    _write_json(
        reports_dir / "discovery_queue_rescoring_pass_report_20260411_v0.json",
        {"summary": {"terminal_route": "HOLD_QUEUE_AFTER_RESCORING", "rank_gap_after_rescoring": 2}},
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["scoring_weight_assessment"] == "REVIEW_WEIGHT_FORMULA_FOR_QUEUE_INCOHERENCE"
    assert report["summary"]["selected_review_disposition"] == "REPAIR_REVIEW_INPUTS_OR_POLICY"
    assert report["summary"]["next_action"] == "RESTORE_REVIEW_INPUTS_AND_REEVALUATE_DISCOVERY_SCORING_ROUTING_ONCE"
