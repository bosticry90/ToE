from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_report as tool,
)


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_shape: bool = True) -> None:
    policy = {
        "required_bounded_check_family_standard_outcome": "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
        "required_repeatability_review_outcome": "LIMITED_HOLD_RETAINED",
        "required_comparator_id": "OV-RL-10",
        "required_bridge_quantity_id": "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
        "required_note_tokens": [
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_ID_v0: rl10_bridge_sigma_db_repeatability_window_check_v0",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_KIND_v0: REPEATABILITY",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_COMPARATOR_v0: OV-RL-10",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_QUANTITY_v0: RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_SCOPE_v0: SINGLE_DECLARED_BRIDGE_SURFACE_AND_ONE_BOUNDED_WINDOW_ONLY",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_BOUNDED_SCOPE_DECLARED_v0: TRUE",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_NON_DISGUISED_SECOND_CYCLE_RULE_v0: THIS_CHECK_IS_NOT_A_FULL_SECOND_EXECUTION_CYCLE",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_FAIL_CLOSED_RULE_v0: IF_SCOPE_EXPANDS_OR_REQUIRES_A_NEW_COMPARATOR_OR_QUANTITY_THE_PATH_REMAINS_HELD",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_STATUS_v0: NAMED_ADMISSIBLE_CHECK_DECLARED_BUT_NOT_YET_EVIDENCE_SUFFICIENT_FOR_STANDARD_APPROVAL",
        ],
        "proposed_check_kind": "REPEATABILITY",
        "proposed_check_name": "rl10_bridge_sigma_db_repeatability_window_check_v0",
        "bounded_scope_declared": True,
        "not_disguised_second_full_cycle_declared": True,
        "path_hold_triggered": False,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("proposed_check_name")

    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_bounded_check_family_standard_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_20260414_v0.json",
                "bridge_repeatability_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_review_20260412_v0.json",
                "named_repeatability_check_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_v0.md",
            },
            "named_repeatability_check_policy": policy,
            "named_repeatability_check_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED",
                    "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_REPAIR",
                ],
                "default_outcome": "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    family_outcome: str = "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED",
    repeatability_review_outcome: str = "LIMITED_HOLD_RETAINED",
    comparator_id: str = "OV-RL-10",
    quantity_id: str = "RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_20260414_v0.json",
        {"summary": {"terminal_outcome": family_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_repeatability_review_20260412_v0.json",
        {
            "summary": {
                "review_outcome": repeatability_review_outcome,
                "external_comparator_id": comparator_id,
                "bridge_quantity_id": quantity_id,
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_v0.md",
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_ID_v0: rl10_bridge_sigma_db_repeatability_window_check_v0\n"
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_KIND_v0: REPEATABILITY\n"
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_COMPARATOR_v0: OV-RL-10\n"
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_QUANTITY_v0: RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0\n"
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_SCOPE_v0: SINGLE_DECLARED_BRIDGE_SURFACE_AND_ONE_BOUNDED_WINDOW_ONLY\n"
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_BOUNDED_SCOPE_DECLARED_v0: TRUE\n"
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_NON_DISGUISED_SECOND_CYCLE_RULE_v0: THIS_CHECK_IS_NOT_A_FULL_SECOND_EXECUTION_CYCLE\n"
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_FAIL_CLOSED_RULE_v0: IF_SCOPE_EXPANDS_OR_REQUIRES_A_NEW_COMPARATOR_OR_QUANTITY_THE_PATH_REMAINS_HELD\n"
        "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_STATUS_v0: NAMED_ADMISSIBLE_CHECK_DECLARED_BUT_NOT_YET_EVIDENCE_SUFFICIENT_FOR_STANDARD_APPROVAL\n",
    )


def test_reports_first_named_repeatability_check_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED"
    assert report["summary"]["named_check_admissible"] is True


def test_reports_first_named_repeatability_check_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, family_outcome="RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_first_named_repeatability_check_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_20260414_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_REPAIR"