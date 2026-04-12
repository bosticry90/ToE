from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import program_posture_review_packet_report as review_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    blocker_movement_ever_observed: bool,
    measurement_regime_fit_for_purpose_default: bool,
    formal_organization_outpacing_conversion_default: bool,
    observed_nonmoving_attack_classes: list[str],
    nonmoving_attack_class_count_threshold: int,
    default_next_program_mode: str,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_post_architecture_alignment_decision_report": "formal/output/reports/science_post_architecture_alignment_decision_20260411_v0.json",
                "architecture_seam_master_action_alignment_ruling_report": "formal/output/reports/architecture_seam_master_action_alignment_ruling_20260411_v0.json",
                "architecture_level_blocker_diagnosis_packet_report": "formal/output/reports/architecture_level_blocker_diagnosis_packet_20260411_v0.json",
            },
            "review_questions": [
                {
                    "question_id": "Q1",
                    "prompt": "Is the current blocker/movement measurement regime still fit for purpose?",
                    "allowed_answers": [
                        "MEASUREMENT_REGIME_FIT_FOR_PURPOSE",
                        "MEASUREMENT_REGIME_REQUIRES_REVISION",
                    ],
                },
                {
                    "question_id": "Q2",
                    "prompt": "Is the project currently producing formal organization faster than scientific conversion?",
                    "allowed_answers": [
                        "FORMAL_ORGANIZATION_OUTPACING_SCIENTIFIC_CONVERSION",
                        "SCIENTIFIC_CONVERSION_PACING_ACCEPTABLE",
                    ],
                },
                {
                    "question_id": "Q3",
                    "prompt": "What one bounded next program mode should follow posture review?",
                    "allowed_answers": [
                        "REORIENT_MEASUREMENT_REGIME",
                        "REORIENT_ARCHITECTURE_TARGET_SELECTION",
                        "REORIENT_PROGRAM_EXECUTION_MODEL",
                    ],
                },
            ],
            "posture_policy": {
                "nonmoving_attack_class_count_threshold": nonmoving_attack_class_count_threshold,
                "observed_nonmoving_attack_classes": observed_nonmoving_attack_classes,
                "blocker_movement_ever_observed": blocker_movement_ever_observed,
                "formal_organization_outpacing_conversion_default": formal_organization_outpacing_conversion_default,
                "measurement_regime_fit_for_purpose_default": measurement_regime_fit_for_purpose_default,
                "default_next_program_mode": default_next_program_mode,
                "no_loop_rule": "ONE_POSTURE_REVIEW_ONLY",
                "no_further_attack_packets_policy": "NO_FURTHER_ATTACK_PACKETS_UNTIL_POSTURE_RESOLVED",
            },
        },
    )


def _write_minimum_inputs(reports_dir: Path) -> None:
    _write_json(
        reports_dir / "science_post_architecture_alignment_decision_20260411_v0.json",
        {
            "summary": {
                "post_architecture_decision": "PROGRAM_POSTURE_REVIEW_REQUIRED",
                "specific_defect_identified": False,
                "defect_scope": None,
                "selected_next_program_mode": "PROGRAM_POSTURE_REVIEW",
                "next_action": "MATERIALIZE_PROGRAM_POSTURE_REVIEW_PACKET",
            }
        },
    )
    _write_json(
        reports_dir / "architecture_seam_master_action_alignment_ruling_20260411_v0.json",
        {
            "summary": {
                "alignment_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER",
                "execution_classification": "ARCHITECTURE_ALIGNMENT_VALID_BUT_NONMOVING",
                "next_action": "REVIEW_POST_ARCHITECTURE_ALIGNMENT_DECISION_AND_DO_NOT_LOOP_ALIGNMENT_PACKET",
            }
        },
    )
    _write_json(
        reports_dir / "architecture_level_blocker_diagnosis_packet_20260411_v0.json",
        {
            "summary": {
                "packet_outcome": "ARCHITECTURE_LEVEL_BLOCKER_DIAGNOSIS_PACKET_COMPLETE",
                "blocker_conversion_failure_location": "MASTER_ACTION_RESIDUAL_EXTRACTION",
                "movement_filter_defect_identified": False,
                "upstream_missing_unit_identified": True,
                "selected_redesigned_attack_class": "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
                "next_action": "MATERIALIZE_ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS_PACKET",
            }
        },
    )


def test_posture_review_defaults_to_measurement_regime_reorient_when_nonmoving_at_threshold(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "PROGRAM_POSTURE_REVIEW_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        blocker_movement_ever_observed=False,
        measurement_regime_fit_for_purpose_default=False,
        formal_organization_outpacing_conversion_default=True,
        observed_nonmoving_attack_classes=[
            "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
            "QM_BLOCKER_MOVING_TRANCHE",
            "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
            "ARCHITECTURE_SEAM_MASTER_ACTION_ALIGNMENT_ATTACK_CLASS",
        ],
        nonmoving_attack_class_count_threshold=4,
        default_next_program_mode="REORIENT_MEASUREMENT_REGIME",
    )
    _write_minimum_inputs(reports_dir)

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["packet_outcome"] == "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED"
    assert report["summary"]["measurement_regime_fit_for_purpose"] is False
    assert report["summary"]["formal_organization_outpacing_conversion"] is True
    assert report["summary"]["selected_next_program_mode"] == "REORIENT_MEASUREMENT_REGIME"
    assert report["summary"]["no_loop_rule"] == "ONE_POSTURE_REVIEW_ONLY"
    assert report["summary"]["next_action"] == "EXECUTE_POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION"
    assert report["criteria"]["nonmoving_attack_class_count_at_threshold"] is True
    assert report["criteria"]["blocker_movement_ever_observed"] is False


def test_posture_review_routes_to_execution_model_when_measurement_fit_but_org_outpacing(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "PROGRAM_POSTURE_REVIEW_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_declaration(
        declaration_path,
        blocker_movement_ever_observed=False,
        measurement_regime_fit_for_purpose_default=True,
        formal_organization_outpacing_conversion_default=True,
        observed_nonmoving_attack_classes=[
            "PROOF_DEBT_FIRST_FORMAL_CAMPAIGN",
            "QM_BLOCKER_MOVING_TRANCHE",
        ],
        nonmoving_attack_class_count_threshold=4,
        default_next_program_mode="REORIENT_MEASUREMENT_REGIME",
    )
    _write_minimum_inputs(reports_dir)

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["measurement_regime_fit_for_purpose"] is True
    assert report["summary"]["formal_organization_outpacing_conversion"] is True
    assert report["summary"]["selected_next_program_mode"] == "REORIENT_PROGRAM_EXECUTION_MODEL"
