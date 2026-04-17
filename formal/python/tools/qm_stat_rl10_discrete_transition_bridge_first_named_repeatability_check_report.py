from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_REPORT_20260414_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_20260414_v0.json"
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
    policy = dict(declaration.get("named_repeatability_check_policy", {}))
    contract = dict(declaration.get("named_repeatability_check_contract", {}))

    family_standard_path = REPO_ROOT / str(
        required_inputs.get("bridge_bounded_check_family_standard_report", "")
    ).strip()
    repeatability_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_review_report", "")
    ).strip()
    note_path = REPO_ROOT / str(required_inputs.get("named_repeatability_check_note", "")).strip()

    family_standard = _read_json(family_standard_path)
    repeatability_review = _read_json(repeatability_review_path)
    note_text = _read_text(note_path)

    family_standard_summary = dict(family_standard.get("summary", {}))
    repeatability_summary = dict(repeatability_review.get("summary", {}))

    family_standard_outcome = str(family_standard_summary.get("terminal_outcome", "")).strip()
    repeatability_review_outcome = str(repeatability_summary.get("review_outcome", "")).strip()
    observed_comparator_id = str(repeatability_summary.get("external_comparator_id", "")).strip()
    observed_bridge_quantity_id = str(repeatability_summary.get("bridge_quantity_id", "")).strip()

    required_family_standard_outcome = str(
        policy.get("required_bounded_check_family_standard_outcome", "")
    ).strip()
    required_repeatability_review_outcome = str(
        policy.get("required_repeatability_review_outcome", "")
    ).strip()
    required_comparator_id = str(policy.get("required_comparator_id", "")).strip()
    required_bridge_quantity_id = str(policy.get("required_bridge_quantity_id", "")).strip()
    required_note_tokens = list(policy.get("required_note_tokens", []))
    proposed_check_kind = str(policy.get("proposed_check_kind", "")).strip().upper()
    proposed_check_name = str(policy.get("proposed_check_name", "")).strip()
    bounded_scope_declared = bool(policy.get("bounded_scope_declared", False))
    not_disguised_second_full_cycle_declared = bool(
        policy.get("not_disguised_second_full_cycle_declared", False)
    )
    path_hold_triggered = bool(policy.get("path_hold_triggered", False))

    note_tokens_present = all(token in note_text for token in required_note_tokens)

    policy_shape_ok = all(
        key in policy
        for key in [
            "required_bounded_check_family_standard_outcome",
            "required_repeatability_review_outcome",
            "required_comparator_id",
            "required_bridge_quantity_id",
            "required_note_tokens",
            "proposed_check_kind",
            "proposed_check_name",
            "bounded_scope_declared",
            "not_disguised_second_full_cycle_declared",
            "path_hold_triggered",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    named_check_admissible = (
        bool(proposed_check_name)
        and proposed_check_kind == "REPEATABILITY"
        and bounded_scope_declared
        and not_disguised_second_full_cycle_declared
        and not path_hold_triggered
    )

    preconditions_ok = (
        family_standard_outcome == required_family_standard_outcome
        and repeatability_review_outcome == required_repeatability_review_outcome
        and observed_comparator_id == required_comparator_id
        and observed_bridge_quantity_id == required_bridge_quantity_id
        and note_tokens_present
        and named_check_admissible
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(
        contract.get(
            "default_outcome",
            "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_REPAIR"
        next_action = "REPAIR_RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED"
        next_action = "RERUN_NAMING_REVIEW_AND_RETAIN_FAIL_CLOSED_POLICY_UNTIL_MINIMUM_EVIDENCE_IS_DEFINED"
    else:
        terminal_outcome = "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_NAMED_REPEATABILITY_CHECK_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "bounded_check_family_standard_outcome_match": family_standard_outcome
            == required_family_standard_outcome,
            "repeatability_review_outcome_match": repeatability_review_outcome
            == required_repeatability_review_outcome,
            "comparator_id_match": observed_comparator_id == required_comparator_id,
            "bridge_quantity_id_match": observed_bridge_quantity_id == required_bridge_quantity_id,
            "note_tokens_present": note_tokens_present,
            "named_check_admissible": named_check_admissible,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "named_repeatability_check_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "bounded_check_family_standard_outcome": family_standard_outcome,
                "required_bounded_check_family_standard_outcome": required_family_standard_outcome,
                "repeatability_review_outcome": repeatability_review_outcome,
                "required_repeatability_review_outcome": required_repeatability_review_outcome,
                "observed_comparator_id": observed_comparator_id,
                "required_comparator_id": required_comparator_id,
                "observed_bridge_quantity_id": observed_bridge_quantity_id,
                "required_bridge_quantity_id": required_bridge_quantity_id,
                "proposed_check_kind": proposed_check_kind,
                "proposed_check_name": proposed_check_name,
                "bounded_scope_declared": bounded_scope_declared,
                "not_disguised_second_full_cycle_declared": not_disguised_second_full_cycle_declared,
                "path_hold_triggered": path_hold_triggered,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "proposed_check_kind": proposed_check_kind,
            "proposed_check_name": proposed_check_name,
            "named_check_admissible": named_check_admissible,
            "bounded_scope_declared": bounded_scope_declared,
            "not_disguised_second_full_cycle_declared": not_disguised_second_full_cycle_declared,
            "path_hold_triggered": path_hold_triggered,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_bounded_check_family_standard_report": _ptr(family_standard_path),
            "bridge_repeatability_review_report": _ptr(repeatability_review_path),
            "named_repeatability_check_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local first named RL10 bridge repeatability check report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the first named RL10 bridge repeatability check report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_20260414_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_first_named_repeatability_check_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())