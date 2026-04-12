from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_post_multi_lane_structure_convergence_review_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    shared_program_feasible: bool = True,
    separate_programs_feasible: bool = True,
    activate_different_lane: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json"
            },
            "convergence_policy": {
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "shared_structural_pattern_detected": True,
                "shared_model_class_program_feasible": shared_program_feasible,
                "separate_model_class_programs_feasible": separate_programs_feasible,
                "activate_different_existing_lane": activate_different_lane,
                "single_review_only": True,
                "single_outcome_only": True
            },
            "review_contract": {
                "allowed_outcomes": [
                    "NEW_SHARED_MODEL_CLASS_PROGRAM_JUSTIFIED",
                    "SEPARATE_NEW_MODEL_CLASS_PROGRAMS_REQUIRED",
                    "ACTIVATE_DIFFERENT_EXISTING_LANE",
                    "HOLD_AND_REQUIRE_HIGHER_LEVEL_ARCHITECTURE_REVIEW"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_MULTI_LANE_CONVERGENCE_OUTCOME",
                "no_loop_rule": "ONE_POST_MULTI_LANE_CONVERGENCE_REVIEW_ONLY",
                "default_outcome": "HOLD_AND_REQUIRE_HIGHER_LEVEL_ARCHITECTURE_REVIEW"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    qm_stat_outcome: str = "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
    gr_outcome: str = "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
    em_qft_outcome: str = "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": qm_stat_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_row_001_structural_gap_definition_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": gr_outcome,
                "row_001_attack_class_cycling_frozen": True,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "em_qft_higher_level_structure_review_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": em_qft_outcome,
                "em_qft_attack_class_cycling_frozen": True,
            }
        },
    )


def test_reports_new_shared_model_class_program_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_MULTI_LANE_STRUCTURE_CONVERGENCE_REVIEW_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "NEW_SHARED_MODEL_CLASS_PROGRAM_JUSTIFIED"


def test_reports_separate_programs_required(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_MULTI_LANE_STRUCTURE_CONVERGENCE_REVIEW_20260412_v0.json"
    _write_declaration(declaration_path, shared_program_feasible=False, separate_programs_feasible=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SEPARATE_NEW_MODEL_CLASS_PROGRAMS_REQUIRED"


def test_reports_activate_different_lane(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_MULTI_LANE_STRUCTURE_CONVERGENCE_REVIEW_20260412_v0.json"
    _write_declaration(declaration_path, shared_program_feasible=False, separate_programs_feasible=False, activate_different_lane=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ACTIVATE_DIFFERENT_EXISTING_LANE"


def test_reports_hold_when_lane_state_preconditions_fail(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_MULTI_LANE_STRUCTURE_CONVERGENCE_REVIEW_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, gr_outcome="GR_HIGHER_LEVEL_STRUCTURE_DECLARABLE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_AND_REQUIRE_HIGHER_LEVEL_ARCHITECTURE_REVIEW"
