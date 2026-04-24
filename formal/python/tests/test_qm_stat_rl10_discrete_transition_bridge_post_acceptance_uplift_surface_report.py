from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_post_acceptance_uplift_surface_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_limitation_mapping_normalization_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_limitation_mapping_normalization_review_20260422_v0.json",
                "bridge_signal_margin_limitation_acceptance_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_20260422_v1.json",
            },
            "seam_scope": {
                "external_comparator_id": "OV-RL-10",
                "bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            },
            "uplift_surface_policy": {
                "required_normalization_outcome": "LIMITATION_MAPPING_NORMALIZATION_COMPLETED",
                "required_acceptance_outcome": "SIGNAL_MARGIN_LIMITATION_ACCEPTED_AT_CURRENT_CEILING",
                "admissible_evidence_class": "INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT",
                "admissible_evidence_object_id": "RL10_INTERPRETATION_SCOPE_UPLIFT_EVIDENCE_OBJECT_v0",
                "admissible_evidence_object_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_interpretation_scope_uplift_evidence_object_20260422_v0.json",
                "uplift_trigger_condition": "DECLARED_EVIDENCE_OBJECT_PASSES_SINGLE_BOUNDED_UPLIFT_GATE",
                "uplift_success_condition": "LIMITATION_INTERPRETATION_SCOPE_HOLD_REPLACED_BY_DECLARED_POST_ACCEPTANCE_UPLIFT_STATE",
                "falsification_condition": "DECLARED_EVIDENCE_OBJECT_FAILS_GATE_OR_REPRODUCES_ACCEPTED_AT_CURRENT_CEILING_WITHOUT_SCOPE_CHANGE",
                "stop_condition_if_not_met": "REMAIN_TERMINAL_BOUNDED_AND_STOP_UNTIL_NEW_DECLARED_SURFACE",
                "single_bounded_execution_object_only": True,
                "no_expansion_no_rollout_guard": True,
                "implicitly_authorizes_promotion": False,
                "implicitly_authorizes_multi_lane_expansion": False,
                "implicitly_authorizes_rollout": False,
                "non_promotion_non_closure_boundary": True,
            },
            "uplift_surface_contract": {
                "allowed_outcomes": [
                    "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_READY_FOR_BOUNDED_EVIDENCE_OBJECT",
                    "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_INVALID",
                    "POST_ACCEPTANCE_UPLIFT_SURFACE_SCOPE_VIOLATION",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_ACCEPTANCE_UPLIFT_SURFACE_OUTCOME",
                "no_loop_rule": "DECLARATION_ONLY_NO_EXECUTION_WITHIN_THIS_SURFACE",
                "default_outcome": "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_INVALID",
            },
        },
    )


def _seed_normalization_report(
    root: Path,
    *,
    outcome: str = "LIMITATION_MAPPING_NORMALIZATION_COMPLETED",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_mapping_normalization_review_20260422_v0.json",
        {
            "summary": {
                "review_outcome": outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            }
        },
    )


def _seed_acceptance_report(
    root: Path,
    *,
    outcome: str = "SIGNAL_MARGIN_LIMITATION_ACCEPTED_AT_CURRENT_CEILING",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_20260422_v1.json",
        {
            "summary": {
                "review_outcome": outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            }
        },
    )


def test_declaration_ready_when_all_uplift_fields_and_guards_present(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_ACCEPTANCE_UPLIFT_SURFACE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["review_outcome"]
        == "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_READY_FOR_BOUNDED_EVIDENCE_OBJECT"
    )
    assert report["summary"]["no_promotion_claim"] is True
    assert report["summary"]["no_seam_closure"] is True


def test_declaration_invalid_when_promotion_or_expansion_is_implicitly_authorized(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_ACCEPTANCE_UPLIFT_SURFACE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["uplift_surface_policy"]["implicitly_authorizes_promotion"] = True
    _write_json(declaration_path, payload)

    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_INVALID"
    assert report["criteria"]["promotion_expansion_rollout_disallowed"] is False


def test_declaration_invalid_when_falsification_condition_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_ACCEPTANCE_UPLIFT_SURFACE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["uplift_surface_policy"]["falsification_condition"] = ""
    _write_json(declaration_path, payload)

    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_INVALID"
    assert report["criteria"]["declaration_text_fields_present"] is False


def test_declaration_invalid_when_evidence_object_report_not_named(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_ACCEPTANCE_UPLIFT_SURFACE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    payload = json.loads(declaration_path.read_text(encoding="utf-8"))
    payload["uplift_surface_policy"]["admissible_evidence_object_report"] = ""
    _write_json(declaration_path, payload)

    _seed_normalization_report(tmp_path)
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "POST_ACCEPTANCE_UPLIFT_SURFACE_DECLARATION_INVALID"
    assert report["criteria"]["evidence_object_report_named"] is False


def test_scope_violation_when_report_scope_mismatches(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_ACCEPTANCE_UPLIFT_SURFACE_20260422_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_normalization_report(tmp_path, comparator_id="OV-RL-10-ALT")
    _seed_acceptance_report(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "POST_ACCEPTANCE_UPLIFT_SURFACE_SCOPE_VIOLATION"
    assert report["criteria"]["same_comparator_and_quantity_preserved"] is False
