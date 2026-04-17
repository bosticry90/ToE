from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_REPORT_20260414_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_20260414_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("policy_standard_approval_record_surface_policy", {}))
    contract = dict(declaration.get("policy_standard_approval_record_surface_contract", {}))

    approval_criteria_path = REPO_ROOT / str(
        required_inputs.get("bridge_policy_standard_approval_criteria_report", "")
    ).strip()
    note_path = REPO_ROOT / str(
        required_inputs.get("policy_standard_approval_record_surface_note", "")
    ).strip()

    approval_criteria = _read_json(approval_criteria_path)
    note_text = _read_text(note_path)

    approval_criteria_summary = dict(approval_criteria.get("summary", {}))
    approval_criteria_outcome = str(approval_criteria_summary.get("terminal_outcome", "")).strip()

    required_approval_criteria_outcome = str(
        policy.get("required_policy_standard_approval_criteria_outcome", "")
    ).strip()
    required_note_tokens = list(policy.get("required_note_tokens", []))
    policy_standard_approval_record_surface_defined = bool(
        policy.get("policy_standard_approval_record_surface_defined", False)
    )
    policy_standard_approval_recorded = bool(policy.get("policy_standard_approval_recorded", False))

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    policy_shape_ok = all(
        key in policy
        for key in [
            "required_policy_standard_approval_criteria_outcome",
            "required_note_tokens",
            "policy_standard_approval_record_surface_defined",
            "policy_standard_approval_recorded",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    preconditions_ok = (
        approval_criteria_outcome == required_approval_criteria_outcome
        and note_tokens_present
        and policy_standard_approval_record_surface_defined
        and not policy_standard_approval_recorded
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(
        contract.get(
            "default_outcome",
            "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_REPAIR"
        next_action = "REPAIR_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_DECLARED"
        next_action = "RETAIN_FAIL_CLOSED_POLICY_UNTIL_AN_EXPLICIT_APPROVAL_RECORD_IS_WRITTEN_ON_THE_DECLARED_SURFACE"
    else:
        terminal_outcome = "RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "policy_standard_approval_criteria_outcome_match": approval_criteria_outcome
            == required_approval_criteria_outcome,
            "note_tokens_present": note_tokens_present,
            "policy_standard_approval_record_surface_defined": policy_standard_approval_record_surface_defined,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_RL10_BRIDGE_POLICY_STANDARD_APPROVAL_RECORD_SURFACE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "approval_record_surface_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "policy_standard_approval_criteria_outcome": approval_criteria_outcome,
                "required_policy_standard_approval_criteria_outcome": required_approval_criteria_outcome,
                "policy_standard_approval_record_surface_defined": policy_standard_approval_record_surface_defined,
                "policy_standard_approval_recorded": policy_standard_approval_recorded,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "policy_standard_approval_record_surface_defined": policy_standard_approval_record_surface_defined,
            "policy_standard_approval_recorded": policy_standard_approval_recorded,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_policy_standard_approval_criteria_report": _ptr(approval_criteria_path),
            "policy_standard_approval_record_surface_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local RL10 bridge policy standard approval-record surface report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the RL10 bridge policy standard approval-record surface report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_surface_20260414_v0.json",
    )
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
        "qm_stat_rl10_discrete_transition_bridge_policy_standard_approval_record_surface_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())