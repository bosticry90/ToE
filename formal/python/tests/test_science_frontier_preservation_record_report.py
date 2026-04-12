from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_frontier_preservation_record_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    all_active_execution_lanes_closed: bool = True,
    restart_prerequisites_documented: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_post_shared_model_class_frontier_decision_report": "formal/output/reports/science_post_shared_model_class_frontier_decision_20260412_v0.json",
                "shared_model_class_post_refinement_decision_report": "formal/output/reports/shared_model_class_post_refinement_decision_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "preservation_policy": {
                "required_frontier_decision_outcome": "PRESERVE_CURRENT_FRONTIER_AND_STOP_ACTIVE_EXECUTION",
                "required_frontier_next_action": "NO_FURTHER_ACTIVE_EXECUTION_AUTHORIZED",
                "required_post_refinement_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "canonical_commit": "bb83c46",
                "all_active_execution_lanes_closed": all_active_execution_lanes_closed,
                "restart_prerequisites_documented": restart_prerequisites_documented,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "frontier_state": {
                "qm_stat": "parked — EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_row_001": "frozen — GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft": "frozen — EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "shared_model_class": "externally comparable candidate, not probe-ready — HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "active_execution_authorized": False,
                "restart_conditions": [
                    "new_higher_level_policy_or_evidence_standard",
                    "genuinely_new_untouched_lane_identified",
                ],
            },
            "preservation_contract": {
                "allowed_outcomes": [
                    "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
                    "FRONTIER_RECORD_INCOMPLETE",
                    "RESTART_PREREQUISITES_DOCUMENTED",
                    "HOLD_PENDING_EXTERNAL_REVIEW",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_FRONTIER_PRESERVATION_RECORD_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_FRONTIER_PRESERVATION_RECORD_LAYER_ONLY",
                "default_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "science_post_shared_model_class_frontier_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "PRESERVE_CURRENT_FRONTIER_AND_STOP_ACTIVE_EXECUTION",
                "next_action": "NO_FURTHER_ACTIVE_EXECUTION_AUTHORIZED",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"}},
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


def test_frontier_preserved_at_canonical_commit(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_FRONTIER_PRESERVATION_RECORD_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT"
    assert report["summary"]["canonical_commit"] == "bb83c46"


def test_frontier_record_incomplete_when_lanes_not_closed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_FRONTIER_PRESERVATION_RECORD_20260412_v0.json"
    )
    _write_declaration(declaration_path, all_active_execution_lanes_closed=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "FRONTIER_RECORD_INCOMPLETE"


def test_restart_prerequisites_documented_when_flag_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_FRONTIER_PRESERVATION_RECORD_20260412_v0.json"
    )
    _write_declaration(declaration_path, restart_prerequisites_documented=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RESTART_PREREQUISITES_DOCUMENTED"


def test_frontier_record_incomplete_when_precondition_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_FRONTIER_PRESERVATION_RECORD_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)
    # Override frontier decision to a wrong outcome — breaks precondition
    _write_json(
        tmp_path
        / "formal"
        / "output"
        / "reports"
        / "science_post_shared_model_class_frontier_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "REOPEN_DISCOVERY_QUEUE_FOR_NEW_UNTOUCHED_LANE",
                "next_action": "OPEN_ONE_BOUNDED_DISCOVERY_SCORING_LAYER_FOR_NEW_UNTOUCHED_CANDIDATE",
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "FRONTIER_RECORD_INCOMPLETE"
