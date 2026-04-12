from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_common_failure_modes_synthesis_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    policy_lane_required_for_restart: bool = False,
    architecture_review_required: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "shared_model_class_post_refinement_decision_report": "formal/output/reports/shared_model_class_post_refinement_decision_20260412_v0.json",
                "qft_gr_post_refinement_decision_report": "formal/output/reports/qft_gr_post_refinement_decision_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
                "governance_blocker_trend_window_report": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "governance_blocker_closure_map_report": "formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
                "em_qft_interface_alignment_obligation_declaration_report": "formal/output/reports/em_qft_interface_alignment_obligation_declaration_20260412_v0.json",
                "gr_regime_limit_alignment_obligation_declaration_report": "formal/output/reports/gr_regime_limit_alignment_obligation_declaration_20260412_v0.json",
            },
            "synthesis_policy": {
                "required_shared_model_class_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "required_qft_gr_outcome": "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "required_gr_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "required_em_qft_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "required_qm_stat_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "required_trend_movement_status": "FLAT",
                "required_trend_net_delta": 0,
                "required_em_qft_obligation_outcome": "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED",
                "required_gr_obligation_outcome": "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED",
                "required_obligation_type": "THEOREM_LINKED",
                "minimum_blocker_rows": 1,
                "policy_lane_required_for_restart": policy_lane_required_for_restart,
                "architecture_review_required": architecture_review_required,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "failure_mode_taxonomy_contract": {
                "required_taxonomy_keys": [
                    "comparator_residual_tolerance_gap",
                    "externally_comparable_to_probe_ready_transition_gap",
                    "bridge_interface_obligation_non_discharge",
                    "regime_translation_gap",
                    "proof_debt_plateau",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_LAYER_ONLY",
                "allowed_outcomes": [
                    "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED",
                    "COMMON_FAILURE_MODES_EVIDENCE_INCOMPLETE",
                    "REQUIRES_POLICY_LANE_FOR_PROBE_READINESS_STANDARD",
                    "HOLD_PENDING_ARCHITECTURE_REVIEW",
                ],
                "default_outcome": "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED",
            },
        },
    )


def _seed_inputs(root: Path, *, qft_gr_outcome: str = "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": qft_gr_outcome}},
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
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json",
        {
            "trend_summary": {"movement_status": "FLAT"},
            "blocker_counts": {"net_delta": 0},
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json",
        {"rows_total": 11},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_interface_alignment_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED",
                "obligation_type": "THEOREM_LINKED",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_regime_limit_alignment_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED",
                "obligation_type": "THEOREM_LINKED",
            }
        },
    )


def test_reports_common_failure_modes_synthesized_and_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED"


def test_reports_common_failure_modes_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, qft_gr_outcome="AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "COMMON_FAILURE_MODES_EVIDENCE_INCOMPLETE"


def test_reports_requires_policy_lane_for_probe_readiness_standard(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path, policy_lane_required_for_restart=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REQUIRES_POLICY_LANE_FOR_PROBE_READINESS_STANDARD"


def test_reports_hold_pending_architecture_review(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_20260412_v0.json"
    )
    _write_declaration(declaration_path, architecture_review_required=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_ARCHITECTURE_REVIEW"
