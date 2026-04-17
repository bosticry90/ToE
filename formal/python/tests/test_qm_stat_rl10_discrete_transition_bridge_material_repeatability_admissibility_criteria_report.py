from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    qm_stat_rl10_discrete_transition_bridge_material_repeatability_admissibility_criteria_report as tool,
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
        "required_policy_standard_approval_criteria_outcome": "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED",
        "required_note_tokens": [
            "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_ID_v0: RL10_BRIDGE_REPEATABILITY_ADMISSIBILITY_CRITERIA",
            "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_SCOPE_v0: ONE_DECLARED_NAMED_REPEATABILITY_CHECK_ON_ONE_DECLARED_BRIDGE_SURFACE",
            "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_COMPARATOR_v0: OV-RL-10",
            "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_QUANTITY_v0: RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0",
            "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_RULE_v0: A_NAMED_REPEATABILITY_CHECK_MUST_BIND_ONE_DECLARED_COMPARATOR_ONE_DECLARED_QUANTITY_AND_ONE_DECLARED_WINDOW",
            "RL10_BRIDGE_MATERIAL_REPEATABILITY_NONEXPANSION_RULE_v0: CRITERIA_MUST_NOT_REQUIRE_A_SECOND_FULL_CYCLE_OR_SCOPE_EXPANSION_TO_BE_DEFINED",
            "RL10_BRIDGE_MATERIAL_REPEATABILITY_POLICY_EFFECT_v0: DEFINES_REPEATABILITY_ADMISSIBILITY_CRITERIA_WITHOUT_SATISFYING_MINIMUM_SECOND_CYCLE_EVIDENCE",
            "RL10_BRIDGE_MATERIAL_REPEATABILITY_STATUS_v0: CRITERIA_DECLARED_BUT_NOT_APPROVAL_SUFFICIENT",
        ],
        "repeatability_admissibility_criteria_defined": True,
        "criteria_nonexpansive": True,
        "criteria_scoped_to_named_check": True,
        "criteria_approval_sufficient": False,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_shape:
        policy.pop("criteria_approval_sufficient")

    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_first_named_repeatability_check_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
                "bridge_policy_standard_approval_criteria_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_20260414_v0.json",
                "material_repeatability_admissibility_criteria_note": "formal/docs/paper/QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_v0.md"
            },
            "material_repeatability_admissibility_policy": policy,
            "material_repeatability_admissibility_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_OUTCOME",
                "no_loop_rule": "ONE_RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_LAYER_ONLY",
                "allowed_outcomes": [
                    "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED",
                    "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_REPAIR"
                ],
                "default_outcome": "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_EVIDENCE_INCOMPLETE"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    named_check_outcome: str = "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED",
    named_check_admissible: bool = True,
    approval_criteria_outcome: str = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_CRITERIA_DECLARED",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": named_check_outcome,
                "named_check_admissible": named_check_admissible,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_criteria_20260414_v0.json",
        {"summary": {"terminal_outcome": approval_criteria_outcome}},
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_v0.md",
        "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_ID_v0: RL10_BRIDGE_REPEATABILITY_ADMISSIBILITY_CRITERIA\n"
        "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_SCOPE_v0: ONE_DECLARED_NAMED_REPEATABILITY_CHECK_ON_ONE_DECLARED_BRIDGE_SURFACE\n"
        "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_COMPARATOR_v0: OV-RL-10\n"
        "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_QUANTITY_v0: RL10_BRIDGE_SIGMA_DB_OBSERVABLE_v0\n"
        "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_RULE_v0: A_NAMED_REPEATABILITY_CHECK_MUST_BIND_ONE_DECLARED_COMPARATOR_ONE_DECLARED_QUANTITY_AND_ONE_DECLARED_WINDOW\n"
        "RL10_BRIDGE_MATERIAL_REPEATABILITY_NONEXPANSION_RULE_v0: CRITERIA_MUST_NOT_REQUIRE_A_SECOND_FULL_CYCLE_OR_SCOPE_EXPANSION_TO_BE_DEFINED\n"
        "RL10_BRIDGE_MATERIAL_REPEATABILITY_POLICY_EFFECT_v0: DEFINES_REPEATABILITY_ADMISSIBILITY_CRITERIA_WITHOUT_SATISFYING_MINIMUM_SECOND_CYCLE_EVIDENCE\n"
        "RL10_BRIDGE_MATERIAL_REPEATABILITY_STATUS_v0: CRITERIA_DECLARED_BUT_NOT_APPROVAL_SUFFICIENT\n",
    )


def test_reports_material_repeatability_admissibility_criteria_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_DECLARED"
    assert report["summary"]["criteria_approval_sufficient"] is False


def test_reports_material_repeatability_admissibility_criteria_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_20260414_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, named_check_outcome="RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_material_repeatability_admissibility_criteria_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_20260414_v0.json"
    _write_declaration(declaration_path, include_full_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_RL10_BRIDGE_MATERIAL_REPEATABILITY_ADMISSIBILITY_CRITERIA_REPAIR"