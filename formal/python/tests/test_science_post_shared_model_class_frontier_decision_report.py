from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_post_shared_model_class_frontier_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    reopen_discovery_queue_for_new_untouched_lane: bool = False,
    open_higher_level_policy_evidence_standard_lane: bool = False,
    require_architecture_review: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "shared_model_class_post_refinement_decision_report": "formal/output/reports/shared_model_class_post_refinement_decision_20260412_v0.json",
                "gr_row_001_structural_gap_definition_report": "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
                "em_qft_higher_level_structure_review_report": "formal/output/reports/em_qft_higher_level_structure_review_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
            },
            "routing_policy": {
                "required_post_refinement_decision_outcome": "HOLD_SHARED_MODEL_CLASS_AS_EXTERNALLY_COMPARABLE_BUT_NOT_PROBE_READY",
                "qm_stat_required_review_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "gr_required_outcome": "GR_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "em_qft_required_outcome": "EM_QFT_REQUIRES_NEW_SEAM_OR_MODEL_CLASS",
                "reopen_discovery_queue_for_new_untouched_lane": reopen_discovery_queue_for_new_untouched_lane,
                "open_higher_level_policy_evidence_standard_lane": open_higher_level_policy_evidence_standard_lane,
                "require_architecture_review": require_architecture_review,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "routing_contract": {
                "allowed_outcomes": [
                    "PRESERVE_CURRENT_FRONTIER_AND_STOP_ACTIVE_EXECUTION",
                    "REOPEN_DISCOVERY_QUEUE_FOR_NEW_UNTOUCHED_LANE",
                    "OPEN_HIGHER_LEVEL_POLICY_EVIDENCE_STANDARD_LANE",
                    "HOLD_AND_REQUIRE_ARCHITECTURE_REVIEW",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_LAYER_ONLY",
                "default_outcome": "PRESERVE_CURRENT_FRONTIER_AND_STOP_ACTIVE_EXECUTION",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
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


def test_preserve_current_frontier_and_stop_active_execution(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "PRESERVE_CURRENT_FRONTIER_AND_STOP_ACTIVE_EXECUTION"


def test_reopen_discovery_queue_for_new_untouched_lane(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, reopen_discovery_queue_for_new_untouched_lane=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "REOPEN_DISCOVERY_QUEUE_FOR_NEW_UNTOUCHED_LANE"


def test_open_higher_level_policy_evidence_standard_lane(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, open_higher_level_policy_evidence_standard_lane=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "OPEN_HIGHER_LEVEL_POLICY_EVIDENCE_STANDARD_LANE"


def test_hold_and_require_architecture_review(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_POST_SHARED_MODEL_CLASS_FRONTIER_DECISION_20260412_v0.json"
    )
    _write_declaration(declaration_path, require_architecture_review=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_AND_REQUIRE_ARCHITECTURE_REVIEW"
