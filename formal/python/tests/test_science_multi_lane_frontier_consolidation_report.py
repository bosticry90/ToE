from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_multi_lane_frontier_consolidation_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    all_current_execution_lanes_closed: bool = True,
    resume_requires_new_policy_or_untouched_lane: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_frontier_preservation_record_report": "formal/output/reports/science_frontier_preservation_record_20260412_v0.json",
                "shared_model_class_post_refinement_decision_report": "formal/output/reports/shared_model_class_post_refinement_decision_20260412_v0.json",
                "qft_gr_post_refinement_decision_report": "formal/output/reports/qft_gr_post_refinement_decision_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "consolidation_policy": {
                "required_frontier_preservation_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
                "required_shared_model_class_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "required_qft_gr_outcome": "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "qft_gr_stop_commit": "2938def",
                "all_current_execution_lanes_closed": all_current_execution_lanes_closed,
                "resume_requires_new_policy_or_untouched_lane": resume_requires_new_policy_or_untouched_lane,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "consolidation_contract": {
                "allowed_outcomes": [
                    "MULTI_LANE_FRONTIER_CONSOLIDATED_AND_CLOSED",
                    "MULTI_LANE_FRONTIER_RECORD_INCOMPLETE",
                    "REQUIRES_HIGHER_LEVEL_POLICY_EVIDENCE_STANDARD_LANE",
                    "HOLD_PENDING_ARCHITECTURE_REVIEW",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_LAYER_ONLY",
                "default_outcome": "MULTI_LANE_FRONTIER_CONSOLIDATED_AND_CLOSED",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    shared_outcome: str = "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
    qft_gr_outcome: str = "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_frontier_preservation_record_20260412_v0.json",
        {"summary": {"terminal_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": shared_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": qft_gr_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "row_001_attack_class_cycling_frozen": True,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_higher_level_structure_review_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_attack_class_cycling_frozen": True,
            }
        },
    )


def test_reports_multi_lane_frontier_consolidated_and_closed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "MULTI_LANE_FRONTIER_CONSOLIDATED_AND_CLOSED"


def test_reports_multi_lane_frontier_record_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_20260412_v0.json"
    )
    _write_declaration(declaration_path, all_current_execution_lanes_closed=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "MULTI_LANE_FRONTIER_RECORD_INCOMPLETE"


def test_reports_requires_higher_level_policy_evidence_standard_lane(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_20260412_v0.json"
    )
    _write_declaration(declaration_path, resume_requires_new_policy_or_untouched_lane=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REQUIRES_HIGHER_LEVEL_POLICY_EVIDENCE_STANDARD_LANE"


def test_reports_multi_lane_frontier_record_incomplete_on_wrong_qft_gr_outcome(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_MULTI_LANE_FRONTIER_CONSOLIDATION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, qft_gr_outcome="AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "MULTI_LANE_FRONTIER_RECORD_INCOMPLETE"
