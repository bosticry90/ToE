from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_restart_anti_alias_proof_declaration_20260419_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _maybe_text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def _all_blank(values: list[str]) -> bool:
    return all(not value.strip() for value in values)


def _all_present(values: list[str]) -> bool:
    return all(value.strip() for value in values)


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("anti_alias_proof_policy", {}))
    contract = dict(declaration.get("anti_alias_proof_outcome_contract", {}))

    trigger_path = REPO_ROOT / _maybe_text(required_inputs.get("science_restart_higher_level_policy_trigger_report"))
    note_path = REPO_ROOT / _maybe_text(required_inputs.get("science_restart_anti_alias_proof_note"))

    trigger_report = _read_json(trigger_path)
    note_text = _read_text(note_path)

    trigger_summary = dict(trigger_report.get("summary", {}))
    trigger_outcome = _maybe_text(trigger_summary.get("terminal_outcome"))
    trigger_family = _maybe_text(trigger_summary.get("trigger_family"))
    higher_level_policy_revision_authorized = bool(
        trigger_summary.get("higher_level_policy_revision_authorized", False)
    )

    required_note_tokens = list(policy.get("required_note_tokens", []))
    required_proof_fields = list(policy.get("required_proof_fields", []))

    anti_alias_proof_declaration_id = _maybe_text(policy.get("anti_alias_proof_declaration_id"))
    anti_alias_proof_summary_reference = _maybe_text(policy.get("anti_alias_proof_summary_reference"))
    field_values = [anti_alias_proof_declaration_id, anti_alias_proof_summary_reference]

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    anti_alias_proof_surface_defined = bool(policy.get("anti_alias_proof_surface_defined", False))
    anti_alias_proof_for_new_candidate_declared = bool(
        policy.get("anti_alias_proof_for_new_candidate_declared", False)
    )
    direct_execution_authorized_now = bool(policy.get("direct_execution_authorized_now", False))
    require_restart_contract_rerun_after_declaration = bool(
        policy.get("require_restart_contract_rerun_after_declaration", False)
    )

    preconditions_ok = (
        trigger_outcome == _maybe_text(policy.get("required_higher_level_policy_trigger_outcome"))
        and higher_level_policy_revision_authorized
        == bool(policy.get("required_higher_level_policy_revision_authorized", False))
        and trigger_family == _maybe_text(policy.get("required_trigger_family"))
        and note_tokens_present
        and anti_alias_proof_surface_defined
        and bool(required_proof_fields)
    )

    fields_all_blank = _all_blank(field_values)
    fields_all_present = _all_present(field_values)

    if fields_all_blank:
        contract_violation = anti_alias_proof_for_new_candidate_declared or direct_execution_authorized_now
    else:
        contract_violation = not all(
            [
                fields_all_present,
                anti_alias_proof_for_new_candidate_declared,
                not direct_execution_authorized_now,
                require_restart_contract_rerun_after_declaration,
            ]
        )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    if not preconditions_ok:
        terminal_outcome = "SCIENCE_RESTART_ANTI_ALIAS_PROOF_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_ANTI_ALIAS_PROOF_PRECONDITIONS_AND_RERUN"
    elif contract_violation:
        terminal_outcome = "SCIENCE_RESTART_ANTI_ALIAS_PROOF_CONTRACT_VIOLATION"
        next_action = "REPAIR_ANTI_ALIAS_PROOF_DECLARATION_FIELDS_AND_FLAGS"
    elif fields_all_present:
        terminal_outcome = "SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARED"
        next_action = "RERUN_RESTART_TRIGGER_CONTRACT_AND_QM_STAT_READINESS_DOSSIER_WITHOUT_DIRECT_EXECUTION_AUTHORIZATION"
    else:
        terminal_outcome = "SCIENCE_RESTART_ANTI_ALIAS_PROOF_READY_BUT_UNDECLARED"
        next_action = "DECLARE_ANTI_ALIAS_PROOF_BEFORE_OPENING_PRE_SCREENING_GATE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "higher_level_policy_trigger_outcome_match": trigger_outcome
            == _maybe_text(policy.get("required_higher_level_policy_trigger_outcome")),
            "higher_level_policy_revision_authorized_match": higher_level_policy_revision_authorized
            == bool(policy.get("required_higher_level_policy_revision_authorized", False)),
            "trigger_family_match": trigger_family == _maybe_text(policy.get("required_trigger_family")),
            "note_tokens_present": note_tokens_present,
            "anti_alias_proof_surface_defined": anti_alias_proof_surface_defined,
            "all_proof_fields_blank": fields_all_blank,
            "all_proof_fields_present": fields_all_present,
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_SCIENCE_RESTART_ANTI_ALIAS_PROOF_DECLARATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "anti_alias_proof_declaration_does_not_authorize_direct_execution": not direct_execution_authorized_now,
            },
            "inputs": {
                "higher_level_policy_trigger_outcome": trigger_outcome,
                "trigger_family": trigger_family,
                "anti_alias_proof_for_new_candidate_declared": anti_alias_proof_for_new_candidate_declared,
                "required_proof_fields": required_proof_fields,
                "direct_execution_authorized_now": direct_execution_authorized_now,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "trigger_family": trigger_family,
            "anti_alias_proof_surface_defined": anti_alias_proof_surface_defined,
            "anti_alias_proof_for_new_candidate_declared": anti_alias_proof_for_new_candidate_declared,
            "anti_alias_proof_declaration_id": anti_alias_proof_declaration_id or None,
            "anti_alias_proof_summary_reference": anti_alias_proof_summary_reference or None,
            "direct_execution_authorized_now": False,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_restart_higher_level_policy_trigger_report": _ptr(trigger_path),
            "science_restart_anti_alias_proof_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local anti-alias proof declaration report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate science restart anti-alias proof declaration report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "science_restart_anti_alias_proof_declaration_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())