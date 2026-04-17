from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    policy = {
        "required_repeatability_review_outcome": "LIMITED_HOLD_RETAINED",
        "allowed_naming_review_outcomes": [
            "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
            "BOUNDED_REPEATABILITY_CHECK_NAMED",
            "BOUNDED_CROSS_PROBE_CHECK_NAMED",
        ],
        "required_baseline_comparator_id": "OV-RL-10",
        "required_bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
        "required_note_tokens": [
            "RL10_BRIDGE_BOUNDED_CHECK_DECLARATION_STANDARD_v0: DECLARE_ONE_SINGLE_SURFACE_SINGLE_COMPARATOR_SINGLE_QUANTITY_CHECK_FAMILY",
            "RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_SURFACE_v0: OV_RL10_TO_RL10_BRIDGE_SIGMA_DB_SINGLE_SURFACE",
            "RL10_BRIDGE_FIRST_BOUNDED_CHECK_FAMILY_v0: REPEATABILITY_STABILITY_WINDOW_FAMILY",
            "RL10_BRIDGE_BOUNDED_CHECK_SCOPE_RULE_v0: ONE_BOUNDED_WINDOW_OR_ONE_BOUNDED_CROSS_PROBE_SLICE_ONLY",
            "RL10_BRIDGE_NON_DISGUISED_SECOND_CYCLE_RULE_v0: NO_FULL_SECOND_EXECUTION_CYCLE_MAY_BE_RELABELED_AS_A_BOUNDED_CHECK",
            "RL10_BRIDGE_FAIL_CLOSED_RULE_v0: IF_SINGLE_SURFACE_OR_SINGLE_COMPARATOR_BREAKS_HOLD_THE_POLICY_PATH_CLOSED",
            "RL10_BRIDGE_NEXT_REQUIRED_OBJECT_v0: NAME_ONE_ADMISSIBLE_CHECK_WITHIN_THE_DECLARED_REPEATABILITY_FAMILY",
            "RL10_BRIDGE_NEXT_REQUIRED_EVIDENCE_v0: DEFINE_MINIMUM_SECOND_CYCLE_EVIDENCE_BEFORE_ANY_STANDARD_APPROVAL",
        ],
        "declaration_standard_id": "RL10_BRIDGE_BOUNDED_CHECK_DECLARATION_STANDARD_v0",
        "policy_surface_id": "OV_RL10_TO_RL10_BRIDGE_SIGMA_DB_SINGLE_SURFACE",
        "first_bounded_check_family_id": "REPEATABILITY_STABILITY_WINDOW_FAMILY",
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("policy_surface_id")

    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_repeatability_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_review_20260412_v0.json",
                "bridge_repeatability_check_naming_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
                "bounded_check_family_standard_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_v0.md",
            },
            "bounded_check_family_policy": policy,
            "bounded_check_family_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
                    "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_REPAIR",
                ],
                "default_outcome": "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    repeatability_review_outcome: str = "LIMITED_HOLD_RETAINED",
    naming_review_outcome: str = "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
    baseline_comparator_id: str = "OV-RL-10",
    bridge_quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_repeatability_review_20260412_v0.json",
        {
            "summary": {"review_outcome": repeatability_review_outcome},
            "objective_quality": {
                "inputs": {
                    "observed_comparator_id": baseline_comparator_id,
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
        {
            "summary": {"review_outcome": naming_review_outcome},
            "objective_quality": {
                "inputs": {
                    "observed_comparator_id": baseline_comparator_id,
                    "observed_quantity_id": bridge_quantity_id,
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "baseline_id": baseline_comparator_id,
                "observable_id": bridge_quantity_id,
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_v0.md",
        "RL10_BRIDGE_BOUNDED_CHECK_DECLARATION_STANDARD_v0: DECLARE_ONE_SINGLE_SURFACE_SINGLE_COMPARATOR_SINGLE_QUANTITY_CHECK_FAMILY\n"
        "RL10_BRIDGE_EXTERNAL_VALIDATION_POLICY_SURFACE_v0: OV_RL10_TO_RL10_BRIDGE_SIGMA_DB_SINGLE_SURFACE\n"
        "RL10_BRIDGE_FIRST_BOUNDED_CHECK_FAMILY_v0: REPEATABILITY_STABILITY_WINDOW_FAMILY\n"
        "RL10_BRIDGE_BOUNDED_CHECK_SCOPE_RULE_v0: ONE_BOUNDED_WINDOW_OR_ONE_BOUNDED_CROSS_PROBE_SLICE_ONLY\n"
        "RL10_BRIDGE_NON_DISGUISED_SECOND_CYCLE_RULE_v0: NO_FULL_SECOND_EXECUTION_CYCLE_MAY_BE_RELABELED_AS_A_BOUNDED_CHECK\n"
        "RL10_BRIDGE_FAIL_CLOSED_RULE_v0: IF_SINGLE_SURFACE_OR_SINGLE_COMPARATOR_BREAKS_HOLD_THE_POLICY_PATH_CLOSED\n"
        "RL10_BRIDGE_NEXT_REQUIRED_OBJECT_v0: NAME_ONE_ADMISSIBLE_CHECK_WITHIN_THE_DECLARED_REPEATABILITY_FAMILY\n"
        "RL10_BRIDGE_NEXT_REQUIRED_EVIDENCE_v0: DEFINE_MINIMUM_SECOND_CYCLE_EVIDENCE_BEFORE_ANY_STANDARD_APPROVAL\n",
    )


def test_reports_bounded_check_family_standard_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_20260414_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED"
    assert report["summary"]["declaration_standard_defined"] is True


def test_reports_bounded_check_family_standard_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_20260414_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, repeatability_review_outcome="PATH_FALSIFIED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_EVIDENCE_INCOMPLETE"


def test_reports_bounded_check_family_standard_remains_declared_after_naming_advances(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_20260414_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, naming_review_outcome="BOUNDED_REPEATABILITY_CHECK_NAMED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED"


def test_reports_hold_pending_bounded_check_family_standard_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_20260414_v0.json"
    )
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_REPAIR"