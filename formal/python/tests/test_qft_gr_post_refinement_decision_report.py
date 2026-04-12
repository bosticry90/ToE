from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qft_gr_post_refinement_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    one_more_refinement_justified: bool = False,
    higher_level_comparator_policy_required: bool = False,
    path_falsified: bool = False,
    consecutive_partial_hold_count: int = 2,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "qft_gr_comparator_binding_execution_report": "formal/output/reports/qft_gr_comparator_binding_execution_20260412_v0.json",
                "qft_gr_binding_refinement_report": "formal/output/reports/qft_gr_binding_refinement_20260412_v0.json",
                "qft_gr_post_signal_interpretation_report": "formal/output/reports/qft_gr_post_signal_interpretation_20260412_v0.json",
                "qft_gr_first_test_packet_report": "formal/output/reports/qft_gr_first_test_packet_20260412_v0.json",
                "science_new_untouched_lane_selection_report": "formal/output/reports/science_new_untouched_lane_selection_20260412_v0.json",
                "science_frontier_preservation_record_report": "formal/output/reports/science_frontier_preservation_record_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "decision_policy": {
                "required_binding_outcome": "QFT_GR_BINDING_PARTIAL_HOLD",
                "required_refinement_outcome": "QFT_GR_BINDING_STILL_PARTIAL_HOLD",
                "required_refinement_next_action": "OPEN_QFT_GR_POST_REFINEMENT_DECISION_LAYER",
                "required_interpretation_outcome": "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE",
                "required_first_test_outcome": "QFT_GR_SEAM_SIGNAL_PRODUCED",
                "required_lane_selection_outcome": "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
                "required_preservation_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "consecutive_partial_hold_count": consecutive_partial_hold_count,
                "one_more_refinement_justified": one_more_refinement_justified,
                "higher_level_comparator_policy_required": higher_level_comparator_policy_required,
                "path_falsified": path_falsified,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "decision_contract": {
                "allowed_outcomes": [
                    "AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT",
                    "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                    "REQUIRES_HIGHER_LEVEL_COMPARATOR_POLICY",
                    "QFT_GR_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QFT_GR_POST_REFINEMENT_DECISION_OUTCOME",
                "no_loop_rule": "ONE_QFT_GR_POST_REFINEMENT_DECISION_LAYER_ONLY",
                "default_outcome": "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
            },
        },
    )


def _seed_inputs(root: Path, *, refinement_outcome: str = "QFT_GR_BINDING_STILL_PARTIAL_HOLD") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_comparator_binding_execution_20260412_v0.json",
        {"summary": {"terminal_outcome": "QFT_GR_BINDING_PARTIAL_HOLD"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_binding_refinement_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": refinement_outcome,
                "next_action": "OPEN_QFT_GR_POST_REFINEMENT_DECISION_LAYER",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_post_signal_interpretation_20260412_v0.json",
        {"summary": {"terminal_outcome": "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_first_test_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": "QFT_GR_SEAM_SIGNAL_PRODUCED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_new_untouched_lane_selection_20260412_v0.json",
        {"summary": {"terminal_outcome": "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST", "selected_lane": "QFT-GR"}},
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


def test_reports_hold_as_externally_comparable_not_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QFT_GR_POST_REFINEMENT_DECISION_20260412_v0.json"
    _write_declaration(declaration_path, one_more_refinement_justified=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_QFT_GR_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"


def test_reports_authorize_one_more_bounded_refinement(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QFT_GR_POST_REFINEMENT_DECISION_20260412_v0.json"
    _write_declaration(declaration_path, one_more_refinement_justified=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "AUTHORIZE_ONE_MORE_BOUNDED_REFINEMENT"


def test_reports_requires_higher_level_comparator_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QFT_GR_POST_REFINEMENT_DECISION_20260412_v0.json"
    _write_declaration(declaration_path, higher_level_comparator_policy_required=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REQUIRES_HIGHER_LEVEL_COMPARATOR_POLICY"


def test_reports_qft_gr_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QFT_GR_POST_REFINEMENT_DECISION_20260412_v0.json"
    _write_declaration(declaration_path, path_falsified=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_PATH_FALSIFIED"
