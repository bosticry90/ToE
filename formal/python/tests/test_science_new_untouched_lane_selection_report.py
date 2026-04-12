from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_new_untouched_lane_selection_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    qft_gr_untouched: bool = True,
    cosmo_sr_untouched: bool = True,
    no_genuinely_untouched_lane: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_frontier_preservation_record_report": "formal/output/reports/science_frontier_preservation_record_20260412_v0.json",
                "shared_model_class_post_refinement_decision_report": "formal/output/reports/shared_model_class_post_refinement_decision_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "selection_policy": {
                "required_preservation_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
                "required_post_refinement_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "excluded_lanes": ["QM-STAT", "GR-ROW-001", "EM-QFT", "SHARED-MODEL-CLASS"],
                "qft_gr_untouched": qft_gr_untouched,
                "cosmo_sr_untouched": cosmo_sr_untouched,
                "no_genuinely_untouched_lane": no_genuinely_untouched_lane,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "selection_contract": {
                "allowed_outcomes": [
                    "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
                    "ACTIVATE_COSMO_SR_UNTOUCHED_FIRST_TEST",
                    "ACTIVATE_OTHER_UNTOUCHED_LANE",
                    "NO_GENUINELY_UNTOUCHED_LANE_AVAILABLE",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_LAYER_ONLY",
                "default_outcome": "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_frontier_preservation_record_20260412_v0.json",
        {"summary": {"terminal_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "shared_model_class_post_refinement_decision_20260412_v0.json",
        {"summary": {"terminal_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY"}},
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


def test_activate_qft_gr_untouched_first_test(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, qft_gr_untouched=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ACTIVATE_QFT_GR_UNTOUCHED_FIRST_TEST"
    assert report["summary"]["selected_lane"] == "QFT-GR"


def test_activate_cosmo_sr_when_qft_gr_not_untouched(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, qft_gr_untouched=False, cosmo_sr_untouched=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ACTIVATE_COSMO_SR_UNTOUCHED_FIRST_TEST"
    assert report["summary"]["selected_lane"] == "COSMO-SR"


def test_activate_other_untouched_lane_when_neither_primary(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, qft_gr_untouched=False, cosmo_sr_untouched=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ACTIVATE_OTHER_UNTOUCHED_LANE"


def test_no_genuinely_untouched_lane_available(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_NEW_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
    )
    _write_declaration(declaration_path, no_genuinely_untouched_lane=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "NO_GENUINELY_UNTOUCHED_LANE_AVAILABLE"
