from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qft_gr_post_signal_interpretation_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    signal_internal_coherence: bool = True,
    external_comparator_candidate_ready: bool = True,
    probe_readiness_ready: bool = False,
    signal_strength_sufficient: bool = True,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "qft_gr_first_test_packet_report": "formal/output/reports/qft_gr_first_test_packet_20260412_v0.json",
                "science_new_untouched_lane_selection_report": "formal/output/reports/science_new_untouched_lane_selection_20260412_v0.json",
                "science_frontier_preservation_record_report": "formal/output/reports/science_frontier_preservation_record_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "interpretation_policy": {
                "required_first_test_outcome": "QFT_GR_SEAM_SIGNAL_PRODUCED",
                "required_lane_selection_outcome": "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
                "required_preservation_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "signal_internal_coherence": signal_internal_coherence,
                "external_comparator_candidate_ready": external_comparator_candidate_ready,
                "probe_readiness_ready": probe_readiness_ready,
                "signal_strength_sufficient": signal_strength_sufficient,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "interpretation_contract": {
                "allowed_outcomes": [
                    "QFT_GR_INTERNAL_SIGNAL_ONLY",
                    "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE",
                    "QFT_GR_PROBE_READY",
                    "QFT_GR_SIGNAL_INSUFFICIENT_HOLD",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QFT_GR_POST_SIGNAL_INTERPRETATION_OUTCOME",
                "no_loop_rule": "ONE_QFT_GR_POST_SIGNAL_INTERPRETATION_LAYER_ONLY",
                "default_outcome": "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
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


def test_qft_gr_externally_comparable_candidate(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QFT_GR_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
    )
    _write_declaration(declaration_path, external_comparator_candidate_ready=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_EXTERNALLY_COMPARABLE_CANDIDATE"


def test_qft_gr_probe_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QFT_GR_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
    )
    _write_declaration(declaration_path, probe_readiness_ready=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_PROBE_READY"


def test_qft_gr_internal_signal_only(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QFT_GR_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        external_comparator_candidate_ready=False,
        signal_internal_coherence=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_INTERNAL_SIGNAL_ONLY"


def test_qft_gr_signal_insufficient_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QFT_GR_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
    )
    _write_declaration(declaration_path, signal_strength_sufficient=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "QFT_GR_SIGNAL_INSUFFICIENT_HOLD"
