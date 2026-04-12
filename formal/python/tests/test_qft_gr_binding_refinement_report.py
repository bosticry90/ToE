from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qft_gr_binding_refinement_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    binding_confirmed: bool = False,
    probe_ready: bool = False,
    binding_still_partial_hold: bool = True,
    requires_undeclared_structure: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "qft_gr_comparator_binding_execution_report": "formal/output/reports/qft_gr_comparator_binding_execution_20260412_v0.json",
                "qft_gr_post_signal_interpretation_report": "formal/output/reports/qft_gr_post_signal_interpretation_20260412_v0.json",
                "qft_gr_first_test_packet_report": "formal/output/reports/qft_gr_first_test_packet_20260412_v0.json",
                "science_new_untouched_lane_selection_report": "formal/output/reports/science_new_untouched_lane_selection_20260412_v0.json",
                "science_frontier_preservation_record_report": "formal/output/reports/science_frontier_preservation_record_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "refinement_policy": {
                "required_binding_outcome": "QFT_GR_BINDING_PARTIAL_HOLD",
                "required_binding_next_action": "OPEN_ONE_BOUNDED_QFT_GR_BINDING_REFINEMENT_LAYER",
                "required_interpretation_outcome": "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE",
                "required_first_test_outcome": "QFT_GR_SEAM_SIGNAL_PRODUCED",
                "required_lane_selection_outcome": "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
                "required_preservation_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "binding_lock": {
                    "seam_id": "QFT-GR",
                    "comparator_id": "EXT-COMP-QFT-GR-0001",
                    "quantity_id": "qft_gr_bridge_transport_interface_residual",
                },
                "binding_weakness": {
                    "weakness_id": "qft_gr_transport_residual_tolerance_gap",
                    "description": "desc",
                },
                "single_refinement": {
                    "refinement_id": "qft_gr_single_weighted_residual_calibration",
                    "description": "desc",
                },
                "single_comparator_only": True,
                "single_quantity_only": True,
                "no_scope_widening": True,
                "refinement_executable_under_declared_structure": True,
                "binding_confirmed": binding_confirmed,
                "probe_ready": probe_ready,
                "binding_still_partial_hold": binding_still_partial_hold,
                "requires_undeclared_structure": requires_undeclared_structure,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "refinement_contract": {
                "allowed_outcomes": [
                    "QFT_GR_BINDING_CONFIRMED",
                    "QFT_GR_PROBE_READY",
                    "QFT_GR_BINDING_STILL_PARTIAL_HOLD",
                    "QFT_GR_REFINEMENT_REQUIRES_UNDECLARED_STRUCTURE",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QFT_GR_BINDING_REFINEMENT_OUTCOME",
                "no_loop_rule": "ONE_QFT_GR_BINDING_REFINEMENT_LAYER_ONLY",
                "default_outcome": "QFT_GR_BINDING_STILL_PARTIAL_HOLD",
            },
        },
    )


def _seed_inputs(root: Path, *, binding_outcome: str = "QFT_GR_BINDING_PARTIAL_HOLD") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qft_gr_comparator_binding_execution_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": binding_outcome,
                "next_action": "OPEN_ONE_BOUNDED_QFT_GR_BINDING_REFINEMENT_LAYER",
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


def test_reports_qft_gr_binding_still_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QFT_GR_BINDING_REFINEMENT_20260412_v0.json"
    _write_declaration(declaration_path, binding_confirmed=False, binding_still_partial_hold=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_BINDING_STILL_PARTIAL_HOLD"


def test_reports_qft_gr_binding_confirmed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QFT_GR_BINDING_REFINEMENT_20260412_v0.json"
    _write_declaration(declaration_path, binding_confirmed=True, binding_still_partial_hold=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_BINDING_CONFIRMED"


def test_reports_qft_gr_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QFT_GR_BINDING_REFINEMENT_20260412_v0.json"
    _write_declaration(declaration_path, binding_confirmed=True, probe_ready=True, binding_still_partial_hold=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_PROBE_READY"


def test_reports_qft_gr_refinement_requires_undeclared_structure(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QFT_GR_BINDING_REFINEMENT_20260412_v0.json"
    _write_declaration(declaration_path, requires_undeclared_structure=True, binding_still_partial_hold=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_REFINEMENT_REQUIRES_UNDECLARED_STRUCTURE"
