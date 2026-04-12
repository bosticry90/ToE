from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_k_new_lane_design_criteria_synthesis_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    recommend_resume_mode: str = "HIGHER_LEVEL_SELECTION_POLICY_LANE",
    include_all_legacy_lanes: bool = True,
    non_reopen_rule_enforced: bool = True,
) -> None:
    required_legacy_lane_outcomes = {
        "QM-STAT": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
        "GR-ROW-001": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
        "EM-QFT": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
        "SHARED-MODEL-CLASS": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
        "QFT-GR": "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
    }
    if not include_all_legacy_lanes:
        required_legacy_lane_outcomes.pop("QFT-GR")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_j_untouched_lane_post_refinement_decision_report": "formal/output/reports/science_phase_j_untouched_lane_post_refinement_decision_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
                "science_phase_d_untouched_lane_selection_report": "formal/output/reports/science_phase_d_untouched_lane_selection_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "shared_model_class_post_refinement_decision_report": "formal/output/reports/shared_model_class_post_refinement_decision_20260412_v0.json",
                "qft_gr_post_refinement_decision_report": "formal/output/reports/qft_gr_post_refinement_decision_20260412_v0.json",
            },
            "synthesis_policy": {
                "required_phase_j_outcome": "HOLD_UNTOUCHED_LANE_AS_VALID_BUT_NONMOVING",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_phase_d_selection_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "required_legacy_lane_outcomes": required_legacy_lane_outcomes,
                "required_held_untouched_lane": "LANE-NEUTRINO-INTERFACE-001",
                "non_reopen_rule_enforced": non_reopen_rule_enforced,
                "recommend_resume_mode": recommend_resume_mode,
                "criteria_axes": [
                    "discriminative_observable_strength",
                    "external_comparator_path_clarity",
                    "declared_structure_sufficiency",
                    "attack_family_mobility",
                ],
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "synthesis_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_LAYER_ONLY",
                "allowed_outcomes": [
                    "NEW_LANE_DESIGN_CRITERIA_SYNTHESIZED_AND_LOCKED",
                    "NEW_LANE_DESIGN_CRITERIA_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_SYNTHESIS_REPAIR",
                ],
                "default_outcome": "NEW_LANE_DESIGN_CRITERIA_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, phase_j_outcome: str = "HOLD_UNTOUCHED_LANE_AS_VALID_BUT_NONMOVING") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_j_untouched_lane_post_refinement_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_j_outcome,
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_d_untouched_lane_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "untouched_lane_candidate_id": "LANE-NEUTRINO-INTERFACE-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {"summary": {"terminal_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_higher_level_structure_review_20260412_v0.json",
        {"summary": {"terminal_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_post_refinement_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"}},
    )


def test_reports_new_lane_design_criteria_synthesized_and_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "NEW_LANE_DESIGN_CRITERIA_SYNTHESIZED_AND_LOCKED"


def test_reports_new_lane_design_criteria_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_j_outcome="AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "NEW_LANE_DESIGN_CRITERIA_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_synthesis_repair_for_coverage_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_all_legacy_lanes=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_SYNTHESIS_REPAIR"


def test_reports_new_lane_design_criteria_evidence_incomplete_when_non_reopen_unenforced(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_K_NEW_LANE_DESIGN_CRITERIA_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path, non_reopen_rule_enforced=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "NEW_LANE_DESIGN_CRITERIA_EVIDENCE_INCOMPLETE"
