from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_REPORT_20260414_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_20260414_v0.json"
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
    policy = dict(declaration.get("minimum_second_cycle_evidence_policy", {}))
    contract = dict(declaration.get("minimum_second_cycle_evidence_contract", {}))

    named_check_path = REPO_ROOT / str(
        required_inputs.get("bridge_first_named_repeatability_check_report", "")
    ).strip()
    family_standard_path = REPO_ROOT / str(
        required_inputs.get("bridge_bounded_check_family_standard_report", "")
    ).strip()
    note_path = REPO_ROOT / str(
        required_inputs.get("minimum_second_cycle_evidence_object_note", "")
    ).strip()

    named_check = _read_json(named_check_path)
    family_standard = _read_json(family_standard_path)
    note_text = _read_text(note_path)

    named_check_summary = dict(named_check.get("summary", {}))
    family_standard_summary = dict(family_standard.get("summary", {}))

    named_check_outcome = str(named_check_summary.get("terminal_outcome", "")).strip()
    family_standard_outcome = str(family_standard_summary.get("terminal_outcome", "")).strip()
    observed_comparator_id = str(named_check_summary.get("proposed_check_name", "")).strip()
    observed_named_check_admissible = bool(named_check_summary.get("named_check_admissible", False))

    required_named_check_outcome = str(
        policy.get("required_named_repeatability_check_outcome", "")
    ).strip()
    required_family_standard_outcome = str(
        policy.get("required_bounded_check_family_standard_outcome", "")
    ).strip()
    required_comparator_id = str(policy.get("required_comparator_id", "")).strip()
    required_bridge_quantity_id = str(policy.get("required_bridge_quantity_id", "")).strip()
    required_note_tokens = list(policy.get("required_note_tokens", []))
    second_cycle_minimum_evidence_defined = bool(
        policy.get("second_cycle_minimum_evidence_defined", False)
    )
    second_cycle_minimum_evidence_satisfied = bool(
        policy.get("second_cycle_minimum_evidence_satisfied", False)
    )

    note_tokens_present = all(token in note_text for token in required_note_tokens)
    comparator_token_present = required_comparator_id in note_text
    quantity_token_present = required_bridge_quantity_id in note_text

    policy_shape_ok = all(
        key in policy
        for key in [
            "required_named_repeatability_check_outcome",
            "required_bounded_check_family_standard_outcome",
            "required_comparator_id",
            "required_bridge_quantity_id",
            "required_note_tokens",
            "second_cycle_minimum_evidence_defined",
            "second_cycle_minimum_evidence_satisfied",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    preconditions_ok = (
        named_check_outcome == required_named_check_outcome
        and family_standard_outcome == required_family_standard_outcome
        and observed_named_check_admissible
        and note_tokens_present
        and comparator_token_present
        and quantity_token_present
        and second_cycle_minimum_evidence_defined
        and not second_cycle_minimum_evidence_satisfied
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(
        contract.get(
            "default_outcome",
            "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_REPAIR"
        next_action = "REPAIR_RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_DECLARED"
        next_action = "RETAIN_FAIL_CLOSED_POLICY_UNTIL_MINIMUM_SECOND_CYCLE_EVIDENCE_IS_MATERIALLY_SATISFIED"
    else:
        terminal_outcome = "RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "named_repeatability_check_outcome_match": named_check_outcome == required_named_check_outcome,
            "bounded_check_family_standard_outcome_match": family_standard_outcome
            == required_family_standard_outcome,
            "named_check_admissible": observed_named_check_admissible,
            "note_tokens_present": note_tokens_present,
            "comparator_token_present": comparator_token_present,
            "quantity_token_present": quantity_token_present,
            "second_cycle_minimum_evidence_defined": second_cycle_minimum_evidence_defined,
            "second_cycle_minimum_evidence_satisfied": second_cycle_minimum_evidence_satisfied,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_RL10_BRIDGE_MINIMUM_SECOND_CYCLE_EVIDENCE_OBJECT_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "minimum_second_cycle_evidence_object_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "named_check_outcome": named_check_outcome,
                "required_named_check_outcome": required_named_check_outcome,
                "family_standard_outcome": family_standard_outcome,
                "required_family_standard_outcome": required_family_standard_outcome,
                "required_comparator_id": required_comparator_id,
                "required_bridge_quantity_id": required_bridge_quantity_id,
                "named_check_admissible": observed_named_check_admissible,
                "second_cycle_minimum_evidence_defined": second_cycle_minimum_evidence_defined,
                "second_cycle_minimum_evidence_satisfied": second_cycle_minimum_evidence_satisfied,
                "named_check_reference": observed_comparator_id,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "second_cycle_minimum_evidence_defined": second_cycle_minimum_evidence_defined,
            "second_cycle_minimum_evidence_satisfied": second_cycle_minimum_evidence_satisfied,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_first_named_repeatability_check_report": _ptr(named_check_path),
            "bridge_bounded_check_family_standard_report": _ptr(family_standard_path),
            "minimum_second_cycle_evidence_object_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local RL10 bridge minimum second-cycle evidence object report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the RL10 bridge minimum second-cycle evidence object report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_20260414_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_minimum_second_cycle_evidence_object_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())