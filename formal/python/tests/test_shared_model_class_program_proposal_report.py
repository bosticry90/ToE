from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import shared_model_class_program_proposal_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    shared_cover: bool = True,
    policy_ready: bool = True,
    include_missing_structure: bool = True,
) -> None:
    shared_missing_structure = ["common-structure"] if include_missing_structure else []
    minimum_components = ["invariant_layer"] if include_missing_structure else []
    first_bounded_test_packet = {
        "packet_id": "SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_20260412_v0",
        "target": "target",
        "acceptance_gate": "gate",
    }
    _write_json(
        path,
        {
            "required_inputs": {
                "science_post_multi_lane_structure_convergence_review_report": "formal/output/reports/science_post_multi_lane_structure_convergence_review_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "proposal_policy": {
                "required_convergence_outcome": "NEW_SHARED_MODEL_CLASS_PROGRAM_JUSTIFIED",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "shared_missing_structure": shared_missing_structure,
                "single_shared_model_class_can_cover_gr_and_em_qft": shared_cover,
                "minimum_model_class_components": minimum_components,
                "first_bounded_test_packet": first_bounded_test_packet,
                "policy_ready_for_proposal": policy_ready,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "proposal_contract": {
                "allowed_outcomes": [
                    "SHARED_MODEL_CLASS_PROPOSAL_JUSTIFIED",
                    "SEPARATE_MODEL_CLASS_PROPOSALS_REQUIRED",
                    "HIGHER_LEVEL_POLICY_REQUIRED_BEFORE_PROPOSAL",
                    "HOLD_AND_DO_NOT_OPEN_MODEL_CLASS_PROGRAM_YET",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SHARED_MODEL_CLASS_PROPOSAL_OUTCOME",
                "no_loop_rule": "ONE_SHARED_MODEL_CLASS_PROPOSAL_LAYER_ONLY",
                "default_outcome": "HOLD_AND_DO_NOT_OPEN_MODEL_CLASS_PROGRAM_YET",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    convergence_outcome: str = "NEW_SHARED_MODEL_CLASS_PROGRAM_JUSTIFIED",
    qm_stat_outcome: str = "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_post_multi_lane_structure_convergence_review_20260412_v0.json",
        {"summary": {"terminal_outcome": convergence_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": qm_stat_outcome}},
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


def test_reports_shared_model_class_proposal_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_PROGRAM_PROPOSAL_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SHARED_MODEL_CLASS_PROPOSAL_JUSTIFIED"


def test_reports_separate_model_class_proposals_required(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_PROGRAM_PROPOSAL_20260412_v0.json"
    _write_declaration(declaration_path, shared_cover=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "SEPARATE_MODEL_CLASS_PROPOSALS_REQUIRED"


def test_reports_higher_level_policy_required_before_proposal(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_PROGRAM_PROPOSAL_20260412_v0.json"
    _write_declaration(declaration_path, policy_ready=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HIGHER_LEVEL_POLICY_REQUIRED_BEFORE_PROPOSAL"


def test_reports_hold_and_do_not_open_when_preconditions_fail(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_PROGRAM_PROPOSAL_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, convergence_outcome="ACTIVATE_DIFFERENT_EXISTING_LANE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_AND_DO_NOT_OPEN_MODEL_CLASS_PROGRAM_YET"
