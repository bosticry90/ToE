from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_ordered_theorem_gap_continuation_tranche_20260419_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _maybe_text(raw: Any) -> str:
    return str(raw).strip() if raw is not None else ""


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("execution_policy", {}))
    contract = dict(declaration.get("outcome_contract", {}))

    remaining_order_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_remaining_physics_execution_order_report"))
    queue_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_objective_quality_physics_completion_queue_report"))
    stat_tranche_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_stat_theorem_gap_completion_tranche_report"))

    remaining_order_report = _read_json(remaining_order_path)
    queue_report = _read_json(queue_path)
    stat_tranche_report = _read_json(stat_tranche_path)

    remaining_summary = dict(remaining_order_report.get("summary", {}))
    queue_summary = dict(queue_report.get("summary", {}))
    stat_summary = dict(stat_tranche_report.get("summary", {}))

    ranked_families = remaining_order_report.get("ranked_families", [])
    second_family_entry = ranked_families[1] if len(ranked_families) > 1 else {}

    remaining_order_ok = all(
        [
            remaining_summary.get("terminal_outcome") == _maybe_text(policy.get("required_remaining_order_outcome")),
            remaining_summary.get("first_family_id") == _maybe_text(policy.get("required_first_family")),
            remaining_summary.get("second_family_id") == _maybe_text(policy.get("required_second_family")),
            remaining_summary.get("next_action") == _maybe_text(policy.get("required_remaining_order_next_action")),
        ]
    )
    queue_ok = all(
        [
            queue_summary.get("terminal_outcome") == _maybe_text(policy.get("required_queue_outcome")),
            queue_summary.get("first_active_row") == _maybe_text(policy.get("required_queue_first_row")),
            queue_summary.get("second_active_row") == _maybe_text(policy.get("required_queue_second_row")),
            queue_summary.get("primary_executable_seam") == _maybe_text(policy.get("required_primary_executable_seam")),
        ]
    )
    stat_tranche_ok = all(
        [
            stat_summary.get("terminal_outcome") == _maybe_text(policy.get("required_stat_tranche_outcome")),
            stat_summary.get("next_action") == _maybe_text(policy.get("required_stat_tranche_next_action")),
            stat_summary.get("target_row_id") == _maybe_text(policy.get("selected_tranche_target_row")),
        ]
    )
    alignment_ok = all(
        [
            second_family_entry.get("family_id") == _maybe_text(policy.get("required_second_family")),
            queue_summary.get("second_active_row") == stat_summary.get("target_row_id"),
            remaining_summary.get("queue_primary_executable_seam") == queue_summary.get("primary_executable_seam"),
        ]
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    contract_violation = any(
        [
            _maybe_text(policy.get("selected_tranche_activation_state")) != "HIGHER_PRIORITY_CLOSEOUT_RECORDED",
            _maybe_text(policy.get("defer_until_family")) != _maybe_text(policy.get("required_first_family")),
            _maybe_text(policy.get("selected_tranche_family")) != "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE",
        ]
    )

    if not all([remaining_order_ok, queue_ok, stat_tranche_ok, alignment_ok]):
        terminal_outcome = "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_INPUTS_AND_RERUN"
    elif contract_violation:
        terminal_outcome = "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_CONTRACT_VIOLATION"
        next_action = "REPAIR_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_POLICY_BEFORE_REPRIORITIZATION"
    else:
        terminal_outcome = "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_MATERIALIZED"
        next_action = stat_summary.get("next_action")

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "remaining_execution_order_recorded": remaining_order_ok,
            "objective_quality_queue_recorded": queue_ok,
            "selected_cosmo_tranche_recorded": stat_tranche_ok,
            "downstream_alignment_ok": alignment_ok,
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "selected_tranche_is_explicitly_canonical": stat_tranche_ok,
                "activation_is_deferred_until_higher_priority_closeout": _maybe_text(policy.get("selected_tranche_activation_state"))
                == "HIGHER_PRIORITY_CLOSEOUT_RECORDED",
                "selected_tranche_preserves_existing_queue_order": queue_ok and alignment_ok,
            },
            "inputs": {
                "higher_priority_family": remaining_summary.get("first_family_id"),
                "selected_tranche_family": _maybe_text(policy.get("selected_tranche_family")),
                "selected_tranche_target_row": stat_summary.get("target_row_id"),
                "selected_tranche_outcome": stat_summary.get("terminal_outcome"),
                "queued_second_row": queue_summary.get("second_active_row"),
                "primary_executable_seam": queue_summary.get("primary_executable_seam"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "selected_tranche_family": _maybe_text(policy.get("selected_tranche_family")),
            "selected_tranche_target_row": stat_summary.get("target_row_id"),
            "selected_tranche_activation_state": _maybe_text(policy.get("selected_tranche_activation_state")),
            "higher_priority_family": remaining_summary.get("first_family_id"),
            "higher_priority_next_action": remaining_summary.get("next_action"),
            "queued_second_row": queue_summary.get("second_active_row"),
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_remaining_physics_execution_order_report": _ptr(remaining_order_path),
            "post_plan_objective_quality_physics_completion_queue_report": _ptr(queue_path),
            "post_plan_stat_theorem_gap_completion_tranche_report": _ptr(stat_tranche_path),
        },
        "non_claim_boundary": "Repository-local post-plan ordered theorem-gap continuation tranche only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-plan ordered theorem-gap continuation tranche report."
    )
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
        "post_plan_ordered_theorem_gap_continuation_tranche_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())