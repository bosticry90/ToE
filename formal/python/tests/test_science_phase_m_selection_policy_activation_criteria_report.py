from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_m_selection_policy_activation_criteria_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    phase_l_authorize_packet_required: bool = False,
    include_complete_groups: bool = True,
) -> None:
    minimum_observable_interface_specificity = [
        "named_observable_interface_contract",
        "explicit_measurement_mapping_for_first_test",
        "declared_pass_fail_discriminator_threshold",
    ]
    if not include_complete_groups:
        minimum_observable_interface_specificity = [
            "named_observable_interface_contract",
            "",
        ]

    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_l_higher_level_selection_policy_report": "formal/output/reports/science_phase_l_higher_level_selection_policy_20260412_v0.json",
                "science_phase_k_new_lane_design_criteria_synthesis_report": "formal/output/reports/science_phase_k_new_lane_design_criteria_synthesis_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
            },
            "activation_contract": {
                "required_phase_l_outcome": "HIGHER_LEVEL_SELECTION_POLICY_DEFINED_AND_LOCKED",
                "required_phase_l_resume_mode": "HIGHER_LEVEL_SELECTION_POLICY_LANE",
                "required_phase_l_authorize_packet": phase_l_authorize_packet_required,
                "required_phase_k_outcome": "NEW_LANE_DESIGN_CRITERIA_SYNTHESIZED_AND_LOCKED",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "activation_criteria_thresholds": {
                    "minimum_discriminativity_prerequisites": [
                        "predeclared_primary_discriminator_with_expected_directionality",
                        "explicit_external_comparator_path_before_first_test",
                        "declared_structure_threshold_above_minimum_sufficiency",
                    ],
                    "minimum_attack_class_admissibility": [
                        "outcome_class_mobility_evidence",
                        "independence_from_prior_closed_lane_aliases",
                        "bounded_measurable_transition_hypothesis",
                    ],
                    "minimum_observable_interface_specificity": minimum_observable_interface_specificity,
                    "minimum_anti_alias_confidence": [
                        "closed_held_lane_alias_risk_low",
                        "boundary_signature_distinct_from_lane_end_family",
                        "non_reopen_policy_compliance_proven",
                    ],
                    "authorize_flip_rule": "AUTHORIZE_ONLY_WHEN_ALL_CRITERIA_GROUPS_SATISFIED",
                },
            },
            "activation_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_LAYER_ONLY",
                "allowed_outcomes": [
                    "SELECTION_POLICY_ACTIVATION_CRITERIA_DEFINED_AND_LOCKED",
                    "SELECTION_POLICY_ACTIVATION_CRITERIA_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_ACTIVATION_CRITERIA_REPAIR",
                ],
                "default_outcome": "SELECTION_POLICY_ACTIVATION_CRITERIA_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    phase_l_outcome: str = "HIGHER_LEVEL_SELECTION_POLICY_DEFINED_AND_LOCKED",
    phase_l_authorize_packet: bool = False,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_l_higher_level_selection_policy_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": phase_l_outcome,
                "resume_mode": "HIGHER_LEVEL_SELECTION_POLICY_LANE",
                "authorize_new_untouched_lane_packet": phase_l_authorize_packet,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_k_new_lane_design_criteria_synthesis_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "NEW_LANE_DESIGN_CRITERIA_SYNTHESIZED_AND_LOCKED",
                "recommend_resume_mode": "HIGHER_LEVEL_SELECTION_POLICY_LANE",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )


def test_reports_selection_policy_activation_criteria_defined_and_locked(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SELECTION_POLICY_ACTIVATION_CRITERIA_DEFINED_AND_LOCKED"
    assert report["summary"]["authorize_new_untouched_lane_packet"] is False


def test_reports_selection_policy_activation_criteria_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase_l_outcome="HIGHER_LEVEL_SELECTION_POLICY_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SELECTION_POLICY_ACTIVATION_CRITERIA_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_activation_criteria_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_complete_groups=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_ACTIVATION_CRITERIA_REPAIR"


def test_reports_selection_policy_activation_criteria_evidence_incomplete_on_phase_l_authorization_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_M_SELECTION_POLICY_ACTIVATION_CRITERIA_20260412_v0.json"
    )
    _write_declaration(declaration_path, phase_l_authorize_packet_required=False)
    _seed_inputs(tmp_path, phase_l_authorize_packet=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SELECTION_POLICY_ACTIVATION_CRITERIA_EVIDENCE_INCOMPLETE"
