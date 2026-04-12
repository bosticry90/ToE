from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qft_gr_first_test_packet_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    movement_signal_detected: bool = True,
    lane_borrows_no_authority_from_frozen_lanes: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_new_untouched_lane_selection_report": "formal/output/reports/science_new_untouched_lane_selection_20260412_v0.json",
                "science_frontier_preservation_record_report": "formal/output/reports/science_frontier_preservation_record_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "test_policy": {
                "required_lane_selection_outcome": "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
                "required_selected_lane": "QFT-GR",
                "required_preservation_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "target_seam": "QFT-GR",
                "single_attack_class": "qft_gr_covariant_bridge_consistency",
                "lane_borrows_no_authority_from_frozen_lanes": lane_borrows_no_authority_from_frozen_lanes,
                "movement_signal_detected": movement_signal_detected,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "test_contract": {
                "allowed_outcomes": [
                    "QFT_GR_SEAM_SIGNAL_PRODUCED",
                    "QFT_GR_SEAM_VALID_BUT_NONMOVING",
                    "QFT_GR_SEAM_REQUIRES_UNDECLARED_STRUCTURE",
                    "QFT_GR_SEAM_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QFT_GR_FIRST_TEST_PACKET_OUTCOME",
                "no_loop_rule": "ONE_QFT_GR_FIRST_TEST_PACKET_LAYER_ONLY",
                "default_outcome": "QFT_GR_SEAM_SIGNAL_PRODUCED",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_new_untouched_lane_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
                "selected_lane": "QFT-GR",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_frontier_preservation_record_20260412_v0.json",
        {"summary": {"terminal_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT"}},
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


def test_qft_gr_seam_signal_produced(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QFT_GR_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path, movement_signal_detected=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_SEAM_SIGNAL_PRODUCED"
    assert report["summary"]["target_seam"] == "QFT-GR"


def test_qft_gr_seam_valid_but_nonmoving(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QFT_GR_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path, movement_signal_detected=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_SEAM_VALID_BUT_NONMOVING"


def test_qft_gr_seam_path_falsified_when_borrows_authority(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QFT_GR_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path, lane_borrows_no_authority_from_frozen_lanes=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_SEAM_PATH_FALSIFIED"


def test_qft_gr_seam_path_falsified_when_precondition_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QFT_GR_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)
    # Break the lane selection outcome
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "science_new_untouched_lane_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "NO_GENUINELY_UNTOUCHED_LANE_AVAILABLE",
                "selected_lane": None,
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_SEAM_PATH_FALSIFIED"
