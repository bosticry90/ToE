from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_restart_anti_alias_proof_declaration_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    anti_alias_proof_declaration_id: str = "",
    anti_alias_proof_summary_reference: str = "",
    anti_alias_proof_for_new_candidate_declared: bool = False,
    direct_execution_authorized_now: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_restart_higher_level_policy_trigger_report": "formal/output/reports/science_restart_higher_level_policy_trigger_20260413_v0.json",
                "science_restart_anti_alias_proof_note": "formal/docs/paper/SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_v0.md",
            },
            "anti_alias_proof_policy": {
                "required_higher_level_policy_trigger_outcome": "HIGHER_LEVEL_POLICY_REVISION_AUTHORIZED",
                "required_higher_level_policy_revision_authorized": True,
                "required_trigger_family": "HIGHER_LEVEL_POLICY_OR_EVIDENCE_STANDARD",
                "required_note_tokens": [
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_ID_v0: SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION",
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_SCOPE_v0: ONE_NEXT_NEW_CANDIDATE_ONLY_NO_DIRECT_EXECUTION_AUTHORIZATION",
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_REQUIRED_FIELDS_v0: ANTI_ALIAS_PROOF_DECLARATION_ID_PLUS_ANTI_ALIAS_PROOF_SUMMARY_REFERENCE",
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_NON_EQUIVALENCE_RULE_v0: ANTI_ALIAS_PROOF_DECLARATION_DOES_NOT_ITSELF_AUTHORIZE_DIRECT_EXECUTION",
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_FAIL_CLOSED_RULE_v0: IF_PROOF_IS_NOT_EXPLICITLY_DECLARED_PRE_SCREENING_GATE_REMAINS_CLOSED",
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_STATUS_v0: DECLARATION_SURFACE_DEFINED_DEFAULT_UNDECLARED",
                ],
                "required_proof_fields": [
                    "anti_alias_proof_declaration_id",
                    "anti_alias_proof_summary_reference",
                ],
                "anti_alias_proof_surface_defined": True,
                "anti_alias_proof_declaration_id": anti_alias_proof_declaration_id,
                "anti_alias_proof_summary_reference": anti_alias_proof_summary_reference,
                "anti_alias_proof_for_new_candidate_declared": anti_alias_proof_for_new_candidate_declared,
                "direct_execution_authorized_now": direct_execution_authorized_now,
                "require_restart_contract_rerun_after_declaration": True,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "anti_alias_proof_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_READY_BUT_UNDECLARED",
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARED",
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_CONTRACT_VIOLATION",
                    "SCIENCE_RESTART_ANTI_ALIAS_PROOF_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "SCIENCE_RESTART_ANTI_ALIAS_PROOF_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    trigger_outcome: str = "HIGHER_LEVEL_POLICY_REVISION_AUTHORIZED",
    higher_level_policy_revision_authorized: bool = True,
    trigger_family: str = "HIGHER_LEVEL_POLICY_OR_EVIDENCE_STANDARD",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_higher_level_policy_trigger_20260413_v0.json",
        {
            "summary": {
                "terminal_outcome": trigger_outcome,
                "higher_level_policy_revision_authorized": higher_level_policy_revision_authorized,
                "trigger_family": trigger_family,
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_v0.md",
        "\n".join(
            [
                "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_ID_v0: SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION",
                "SCIENCE_RESTART_ANTI_ALIAS_PROOF_SCOPE_v0: ONE_NEXT_NEW_CANDIDATE_ONLY_NO_DIRECT_EXECUTION_AUTHORIZATION",
                "SCIENCE_RESTART_ANTI_ALIAS_PROOF_REQUIRED_FIELDS_v0: ANTI_ALIAS_PROOF_DECLARATION_ID_PLUS_ANTI_ALIAS_PROOF_SUMMARY_REFERENCE",
                "SCIENCE_RESTART_ANTI_ALIAS_PROOF_NON_EQUIVALENCE_RULE_v0: ANTI_ALIAS_PROOF_DECLARATION_DOES_NOT_ITSELF_AUTHORIZE_DIRECT_EXECUTION",
                "SCIENCE_RESTART_ANTI_ALIAS_PROOF_FAIL_CLOSED_RULE_v0: IF_PROOF_IS_NOT_EXPLICITLY_DECLARED_PRE_SCREENING_GATE_REMAINS_CLOSED",
                "SCIENCE_RESTART_ANTI_ALIAS_PROOF_STATUS_v0: DECLARATION_SURFACE_DEFINED_DEFAULT_UNDECLARED",
            ]
        ),
    )


def test_reports_ready_but_undeclared_by_default(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_20260419_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "SCIENCE_RESTART_ANTI_ALIAS_PROOF_READY_BUT_UNDECLARED"
    assert report["summary"]["next_action"] == "DECLARE_ANTI_ALIAS_PROOF_BEFORE_OPENING_PRE_SCREENING_GATE"


def test_reports_declared_when_all_fields_are_present(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_20260419_v0.json"
    )
    _write_declaration(
        declaration_path,
        anti_alias_proof_declaration_id="ANTI-ALIAS-PROOF-001",
        anti_alias_proof_summary_reference="formal/docs/paper/ANTI_ALIAS_PROOF_SUMMARY_v0.md",
        anti_alias_proof_for_new_candidate_declared=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARED"


def test_reports_contract_violation_on_partial_or_executing_state(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_20260419_v0.json"
    )
    _write_declaration(
        declaration_path,
        anti_alias_proof_declaration_id="ANTI-ALIAS-PROOF-001",
        anti_alias_proof_summary_reference="",
        anti_alias_proof_for_new_candidate_declared=True,
        direct_execution_authorized_now=True,
    )
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "SCIENCE_RESTART_ANTI_ALIAS_PROOF_CONTRACT_VIOLATION"