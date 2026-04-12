from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qft_gr_comparator_binding_execution_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    binding_confirmed: bool = False,
    binding_partial_evidence: bool = True,
    probe_ready_now: bool = False,
    path_falsified: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "qft_gr_post_signal_interpretation_report": "formal/output/reports/qft_gr_post_signal_interpretation_20260412_v0.json",
                "qft_gr_first_test_packet_report": "formal/output/reports/qft_gr_first_test_packet_20260412_v0.json",
                "science_new_untouched_lane_selection_report": "formal/output/reports/science_new_untouched_lane_selection_20260412_v0.json",
                "science_frontier_preservation_record_report": "formal/output/reports/science_frontier_preservation_record_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "binding_policy": {
                "required_interpretation_outcome": "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE",
                "required_first_test_outcome": "QFT_GR_SEAM_SIGNAL_PRODUCED",
                "required_lane_selection_outcome": "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
                "required_preservation_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "single_comparator": {
                    "comparator_id": "EXT-COMP-QFT-GR-0001",
                    "description": "External comparator focused on QFT-GR bridge transport consistency under bounded mapping",
                },
                "single_bound_quantity": {
                    "quantity_id": "qft_gr_bridge_transport_interface_residual",
                    "description": "Residual on the QFT-GR bridge transport interface under one bounded comparator map",
                },
                "binding_confirmed": binding_confirmed,
                "binding_partial_evidence": binding_partial_evidence,
                "probe_ready_now": probe_ready_now,
                "path_falsified": path_falsified,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "binding_contract": {
                "allowed_outcomes": [
                    "QFT_GR_COMPARATOR_BINDING_CONFIRMED",
                    "QFT_GR_PROBE_READY",
                    "QFT_GR_BINDING_PARTIAL_HOLD",
                    "QFT_GR_PATH_FALSIFIED",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QFT_GR_COMPARATOR_BINDING_EXECUTION_OUTCOME",
                "no_loop_rule": "ONE_QFT_GR_COMPARATOR_BINDING_EXECUTION_LAYER_ONLY",
                "default_outcome": "QFT_GR_BINDING_PARTIAL_HOLD",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
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


def test_reports_qft_gr_binding_partial_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, binding_confirmed=False, binding_partial_evidence=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_BINDING_PARTIAL_HOLD"


def test_reports_qft_gr_comparator_binding_confirmed(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, binding_confirmed=True, binding_partial_evidence=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_COMPARATOR_BINDING_CONFIRMED"


def test_reports_qft_gr_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, probe_ready_now=True, binding_partial_evidence=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_PROBE_READY"


def test_reports_qft_gr_path_falsified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QFT_GR_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, path_falsified=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_PATH_FALSIFIED"
