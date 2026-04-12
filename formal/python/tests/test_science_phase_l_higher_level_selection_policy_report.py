from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_l_higher_level_selection_policy_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    required_lane_end_state_family_size: int = 6,
    forbid_reopen: bool = True,
    forbid_packet_before_gate: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_k_new_lane_design_criteria_synthesis_report": "formal/output/reports/science_phase_k_new_lane_design_criteria_synthesis_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "policy_contract": {
                "required_phase_k_outcome": "NEW_LANE_DESIGN_CRITERIA_SYNTHESIZED_AND_LOCKED",
                "required_phase_k_resume_mode": "HIGHER_LEVEL_SELECTION_POLICY_LANE",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_lane_end_state_family_size": required_lane_end_state_family_size,
                "forbid_closed_or_held_lane_reopen": forbid_reopen,
                "forbid_new_untouched_lane_packet_before_policy_gate": forbid_packet_before_gate,
                "single_layer_only": True,
                "single_outcome_only": True,
                "lane_discriminativity_prerequisites": [
                    "predeclared_primary_discriminator_with_expected_directionality",
                    "explicit_external_comparator_path_before_first_test",
                    "declared_structure_threshold_above_minimum_sufficiency",
                ],
                "acceptable_first_test_attack_class_properties": [
                    "outcome_class_mobility_evidence",
                    "independence_from_prior_closed_lane_aliases",
                    "bounded_measurable_transition_hypothesis",
                ],
                "nonmoving_early_warning_signals": [
                    "first_test_nondiscriminative_hold_without_external_mapping_gain",
                    "attack_reselection_changes_packet_form_without_outcome_class_shift",
                    "refinement_cycle_retains_valid_but_nonmoving_class",
                ],
                "exclude_likely_low_yield_lanes_when": [
                    "no_explicit_discriminator_declared",
                    "external_comparator_route_unspecified",
                    "requires_undeclared_structure_to_progress",
                    "high_alias_risk_to_closed_or_held_lane_family",
                ],
            },
            "selection_policy_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_LAYER_ONLY",
                "allowed_outcomes": [
                    "HIGHER_LEVEL_SELECTION_POLICY_DEFINED_AND_LOCKED",
                    "HIGHER_LEVEL_SELECTION_POLICY_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_SELECTION_POLICY_REPAIR",
                ],
                "default_outcome": "HIGHER_LEVEL_SELECTION_POLICY_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, phase_k_outcome: str = "NEW_LANE_DESIGN_CRITERIA_SYNTHESIZED_AND_LOCKED") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_k_new_lane_design_criteria_synthesis_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_k_outcome,
                "recommend_resume_mode": "HIGHER_LEVEL_SELECTION_POLICY_LANE",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_higher_level_selection_policy_defined_and_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HIGHER_LEVEL_SELECTION_POLICY_DEFINED_AND_LOCKED"
    assert report["summary"]["authorize_new_untouched_lane_packet"] is False


def test_reports_selection_policy_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_k_outcome="NEW_LANE_DESIGN_CRITERIA_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HIGHER_LEVEL_SELECTION_POLICY_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_selection_policy_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_20260412_v0.json"
    )
    _write_declaration(declaration_path, required_lane_end_state_family_size=5)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_SELECTION_POLICY_REPAIR"


def test_reports_selection_policy_evidence_incomplete_when_reopen_guard_unset(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_L_HIGHER_LEVEL_SELECTION_POLICY_20260412_v0.json"
    )
    _write_declaration(declaration_path, forbid_reopen=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HIGHER_LEVEL_SELECTION_POLICY_EVIDENCE_INCOMPLETE"
