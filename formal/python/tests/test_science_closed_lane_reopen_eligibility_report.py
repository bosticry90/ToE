from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_closed_lane_reopen_eligibility_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    selected_reopen_lane: str = "NONE",
    selected_reopen_lane_proof_declared: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "probe_readiness_standard_formalization_report": "formal/output/reports/probe_readiness_standard_formalization_20260412_v0.json",
                "shared_model_class_post_refinement_decision_report": "formal/output/reports/shared_model_class_post_refinement_decision_20260412_v0.json",
                "qft_gr_post_refinement_decision_report": "formal/output/reports/qft_gr_post_refinement_decision_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "eligibility_policy": {
                "required_formalization_outcome": "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED",
                "required_shared_model_class_closed_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "required_qft_gr_closed_outcome": "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "required_gr_closed_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "required_em_qft_closed_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "required_qm_stat_closed_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "authorization_mode": "AT_MOST_ONE",
                "selected_reopen_lane": selected_reopen_lane,
                "selected_reopen_lane_proof_declared": selected_reopen_lane_proof_declared,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "eligibility_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_LAYER_ONLY",
                "allowed_outcomes": [
                    "CLOSED_LANE_REOPEN_NONE_ELIGIBLE",
                    "CLOSED_LANE_REOPEN_ONE_LANE_AUTHORIZED",
                    "CLOSED_LANE_REOPEN_CONTRACT_VIOLATION",
                    "CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    formalization_outcome: str = "PROBE_READINESS_STANDARD_FORMALIZED_AND_LOCKED",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "probe_readiness_standard_formalization_20260412_v0.json",
        {"summary": {"terminal_outcome": formalization_outcome}},
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


def test_reports_closed_lane_reopen_none_eligible(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_20260412_v0.json"
    )
    _write_declaration(declaration_path, selected_reopen_lane="NONE")
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CLOSED_LANE_REOPEN_NONE_ELIGIBLE"


def test_reports_closed_lane_reopen_one_lane_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        selected_reopen_lane="QFT-GR",
        selected_reopen_lane_proof_declared=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CLOSED_LANE_REOPEN_ONE_LANE_AUTHORIZED"


def test_reports_closed_lane_reopen_contract_violation(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        selected_reopen_lane="INVALID-LANE",
        selected_reopen_lane_proof_declared=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CLOSED_LANE_REOPEN_CONTRACT_VIOLATION"


def test_reports_closed_lane_reopen_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        selected_reopen_lane="QFT-GR",
        selected_reopen_lane_proof_declared=False,
    )
    _seed_inputs(tmp_path, formalization_outcome="PROBE_READINESS_STANDARD_FORMALIZATION_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE"
