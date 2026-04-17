from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_restart_higher_level_policy_trigger_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    include_full_contract_shape: bool = True,
    required_policy_standard_formalization_outcome: str = "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED",
    required_policy_standard_approved: bool = False,
) -> None:
    contract = {
        "required_frontier_preservation_outcome": "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
        "required_frontier_next_action": "NO_FURTHER_ACTIVE_EXECUTION_AUTHORIZED_RESUME_FROM_NEW_STANDARD_OR_NEW_LANE",
        "required_restart_condition_token": "new_higher_level_policy_or_evidence_standard",
        "required_policy_standard_formalization_outcome": required_policy_standard_formalization_outcome,
        "required_policy_standard_approved": required_policy_standard_approved,
        "allowed_policy_review_outcomes_for_authorization": [
            "ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED",
            "ADMISSIBLE_CROSS_PROBE_STANDARD_DEFINED",
        ],
        "require_policy_standard_defined": True,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_contract_shape:
        contract.pop("required_restart_condition_token")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_frontier_preservation_record_report": "formal/output/reports/science_frontier_preservation_record_20260412_v0.json",
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
                "bridge_external_validation_policy_standard_formalization_report": "formal/output/reports/bridge_external_validation_policy_standard_formalization_20260413_v0.json",
            },
            "higher_level_policy_trigger_contract": contract,
            "higher_level_policy_trigger_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_HIGHER_LEVEL_POLICY_TRIGGER_OUTCOME",
                "no_loop_rule": "ONE_HIGHER_LEVEL_POLICY_TRIGGER_LAYER_ONLY",
                "allowed_outcomes": [
                    "HIGHER_LEVEL_POLICY_REVISION_AUTHORIZED",
                    "HIGHER_LEVEL_POLICY_REVISION_NOT_AUTHORIZED",
                    "HIGHER_LEVEL_POLICY_REVISION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_HIGHER_LEVEL_POLICY_REVISION_REPAIR",
                ],
                "default_outcome": "HIGHER_LEVEL_POLICY_REVISION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    frontier_outcome: str = "FRONTIER_PRESERVED_AT_CANONICAL_COMMIT",
    frontier_next_action: str = "NO_FURTHER_ACTIVE_EXECUTION_AUTHORIZED_RESUME_FROM_NEW_STANDARD_OR_NEW_LANE",
    restart_conditions: list[str] | None = None,
    review_outcome: str = "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
    policy_standard_formalization_outcome: str = "EXTERNAL_VALIDATION_POLICY_STANDARD_FORMALLY_DEFINED_BUT_NOT_APPROVED",
    policy_standard_defined: bool = True,
    policy_standard_approved: bool = False,
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_frontier_preservation_record_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": frontier_outcome,
                "next_action": frontier_next_action,
            },
            "frontier_state": {
                "restart_conditions": restart_conditions
                if restart_conditions is not None
                else ["new_higher_level_policy_or_evidence_standard", "genuinely_new_untouched_lane_identified"]
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {
            "summary": {"review_outcome": review_outcome},
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_standard_formalization_20260413_v0.json",
        {
            "summary": {
                "terminal_outcome": policy_standard_formalization_outcome,
                "policy_standard_defined": policy_standard_defined,
                "policy_standard_approved": policy_standard_approved,
            }
        },
    )


def test_reports_higher_level_policy_revision_not_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_RESTART_HIGHER_LEVEL_POLICY_TRIGGER_20260413_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HIGHER_LEVEL_POLICY_REVISION_NOT_AUTHORIZED"


def test_reports_higher_level_policy_revision_authorized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_RESTART_HIGHER_LEVEL_POLICY_TRIGGER_20260413_v0.json"
    )
    _write_declaration(
        declaration_path,
        required_policy_standard_formalization_outcome="EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVED_AND_TRIGGER_AUTHORIZED",
        required_policy_standard_approved=True,
    )
    _seed_inputs(
        tmp_path,
        review_outcome="ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED",
        policy_standard_formalization_outcome="EXTERNAL_VALIDATION_POLICY_STANDARD_APPROVED_AND_TRIGGER_AUTHORIZED",
        policy_standard_defined=True,
        policy_standard_approved=True,
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HIGHER_LEVEL_POLICY_REVISION_AUTHORIZED"


def test_reports_higher_level_policy_revision_evidence_incomplete(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_RESTART_HIGHER_LEVEL_POLICY_TRIGGER_20260413_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        frontier_outcome="FRONTIER_RECORD_INCOMPLETE",
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HIGHER_LEVEL_POLICY_REVISION_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_higher_level_policy_revision_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_RESTART_HIGHER_LEVEL_POLICY_TRIGGER_20260413_v0.json"
    )
    _write_declaration(declaration_path, include_full_contract_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_HIGHER_LEVEL_POLICY_REVISION_REPAIR"