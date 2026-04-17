from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    policy = {
        "required_named_repeatability_check_outcome": "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED",
        "required_bounded_check_family_standard_outcome": "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
        "required_comparator_id": "OV-RL-10",
        "required_bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
        "required_note_tokens": [
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_ID_v0: RL10_BRIDGE_SECOND_CYCLE_MINIMUM_EVIDENCE_OBJECT",
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_COMPARATOR_v0: OV-RL-10",
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_QUANTITY_v0: RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_SCOPE_v0: ONE_DECLARED_REPEATABILITY_WINDOW_ON_ONE_DECLARED_BRIDGE_SURFACE",
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_DECLARATION_RULE_v0: DEFINE_THE_MINIMUM_EVIDENCE_OBJECT_BEFORE_ANY_POLICY_STANDARD_APPROVAL",
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_SATISFACTION_RULE_v0: DECLARATION_DOES_NOT_COUNT_AS_SATISFACTION",
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_FAIL_CLOSED_RULE_v0: IF_EVIDENCE_REQUIRES_SCOPE_EXPANSION_OR_A_SECOND_FULL_CYCLE_THE_POLICY_PATH_REMAINS_HELD",
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_STATUS_v0: OBJECT_DECLARED_BUT_NOT_YET_SATISFIED",
        ],
        "second_cycle_minimum_evidence_defined": True,
        "second_cycle_minimum_evidence_satisfied": False,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("second_cycle_minimum_evidence_satisfied")

    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_first_named_repeatability_check_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
                "bridge_bounded_check_family_standard_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_20260414_v0.json",
                "minimum_second_cycle_evidence_object_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_v0.md",
            },
            "minimum_second_cycle_evidence_policy": policy,
            "minimum_second_cycle_evidence_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED",
                    "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_REPAIR",
                ],
                "default_outcome": "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    named_check_outcome: str = "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED",
    named_check_admissible: bool = True,
    family_outcome: str = "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": named_check_outcome,
                "named_check_admissible": named_check_admissible,
                "proposed_check_name": "rl10_bridge_sigma_db_repeatability_window_check_v0",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_20260414_v0.json",
        {"summary": {"terminal_outcome": family_outcome}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_v0.md",
        "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_ID_v0: RL10_BRIDGE_SECOND_CYCLE_MINIMUM_EVIDENCE_OBJECT\n"
        "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_COMPARATOR_v0: OV-RL-10\n"
        "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_QUANTITY_v0: RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0\n"
        "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_SCOPE_v0: ONE_DECLARED_REPEATABILITY_WINDOW_ON_ONE_DECLARED_BRIDGE_SURFACE\n"
        "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_DECLARATION_RULE_v0: DEFINE_THE_MINIMUM_EVIDENCE_OBJECT_BEFORE_ANY_POLICY_STANDARD_APPROVAL\n"
        "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_SATISFACTION_RULE_v0: DECLARATION_DOES_NOT_COUNT_AS_SATISFACTION\n"
        "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_FAIL_CLOSED_RULE_v0: IF_EVIDENCE_REQUIRES_SCOPE_EXPANSION_OR_A_SECOND_FULL_CYCLE_THE_POLICY_PATH_REMAINS_HELD\n"
        "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_STATUS_v0: OBJECT_DECLARED_BUT_NOT_YET_SATISFIED\n",
    )


def test_reports_minimum_second_cycle_evidence_object_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED"
    assert report["summary"]["second_cycle_minimum_evidence_defined"] is True
    assert report["summary"]["second_cycle_minimum_evidence_satisfied"] is False


def test_reports_minimum_second_cycle_evidence_object_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, named_check_outcome="RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_minimum_second_cycle_evidence_object_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_20260414_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_REPAIR"