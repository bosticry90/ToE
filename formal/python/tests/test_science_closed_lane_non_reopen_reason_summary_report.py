from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_closed_lane_non_reopen_reason_summary_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path, *, include_all_required_lanes: bool = True) -> None:
    required_lane_outcomes = {
        "QM-STAT": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
        "GR-ROW-001": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
        "EM-QFT": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
        "SHARED-MODEL-CLASS": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
        "QFT-GR": "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
    }
    if not include_all_required_lanes:
        required_lane_outcomes.pop("QFT-GR")

    _write_json(
        path,
        {
            "required_inputs": {
                "probe_readiness_standard_formalization_report": "formal/output/reports/probe_readiness_standard_formalization_20260412_v0.json",
                "science_closed_lane_reopen_eligibility_report": "formal/output/reports/science_closed_lane_reopen_eligibility_20260412_v0.json",
                "shared_model_class_post_refinement_decision_report": "formal/output/reports/shared_model_class_post_refinement_decision_20260412_v0.json",
                "qft_gr_post_refinement_decision_report": "formal/output/reports/qft_gr_post_refinement_decision_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "summary_policy": {
                "required_formalization_outcome": "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED",
                "required_reopen_eligibility_outcome": "CLOSED_LANE_REOPEN_NONE_ELIGIBLE",
                "required_lane_outcomes": required_lane_outcomes,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "summary_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_OUTCOME",
                "no_loop_rule": "ONE_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LAYER_ONLY",
                "allowed_outcomes": [
                    "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                    "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_INCOMPLETE",
                    "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_CONTRACT_VIOLATION",
                    "HOLD_PENDING_REASON_SUMMARY_REPAIR",
                ],
                "default_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    reopen_outcome: str = "CLOSED_LANE_REOPEN_NONE_ELIGIBLE",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "probe_readiness_standard_formalization_20260412_v0.json",
        {"summary": {"terminal_outcome": "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_reopen_eligibility_20260412_v0.json",
        {"summary": {"terminal_outcome": reopen_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"}},
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
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"}},
    )


def test_reports_closed_lane_non_reopen_reason_summary_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"


def test_reports_closed_lane_non_reopen_reason_summary_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, reopen_outcome="CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_INCOMPLETE"


def test_reports_closed_lane_non_reopen_reason_summary_contract_violation(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)
    em_qft_path = (
        tmp_path / "formal" / "output" / "reports" / "em_qft_higher_level_structure_review_20260412_v0.json"
    )
    em_qft = json.loads(em_qft_path.read_text(encoding="utf-8"))
    em_qft["summary"]["terminal_outcome"] = "MISMATCH"
    em_qft_path.write_text(json.dumps(em_qft, indent=2) + "\n", encoding="utf-8")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_INCOMPLETE"


def test_reports_hold_pending_reason_summary_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_all_required_lanes=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_REASON_SUMMARY_REPAIR"
