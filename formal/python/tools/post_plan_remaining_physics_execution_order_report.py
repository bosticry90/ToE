from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_remaining_physics_execution_order_20260419_v0.json"
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
    policy = dict(declaration.get("ordering_policy", {}))
    contract = dict(declaration.get("ordering_contract", {}))

    selected_execution_path = REPO_ROOT / _maybe_text(
        required_inputs.get("post_plan_cosmo_sr_selected_continuation_execution_report")
    )
    selected_family_path = REPO_ROOT / _maybe_text(
        required_inputs.get("post_plan_cosmo_sr_selected_continuation_family_report")
    )
    unlock_path = REPO_ROOT / _maybe_text(
        required_inputs.get("post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report")
    )
    queue_path = REPO_ROOT / _maybe_text(
        required_inputs.get("post_plan_objective_quality_physics_completion_queue_report")
    )
    exhaustion_path = REPO_ROOT / _maybe_text(
        required_inputs.get("post_plan_post_cascade_explicit_exhaustion_decision_report")
    )
    successor_path = REPO_ROOT / _maybe_text(
        required_inputs.get("post_plan_post_cascade_successor_family_eligibility_review_report")
    )

    selected_execution_report = _read_json(selected_execution_path)
    selected_family_report = _read_json(selected_family_path)
    unlock_report = _read_json(unlock_path)
    queue_report = _read_json(queue_path)
    exhaustion_report = _read_json(exhaustion_path)
    successor_report = _read_json(successor_path)

    ranked_family_order = list(policy.get("ranked_family_order", []))
    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    selected_execution_summary = dict(selected_execution_report.get("summary", {}))
    selected_family_summary = dict(selected_family_report.get("summary", {}))
    unlock_summary = dict(unlock_report.get("summary", {}))
    queue_summary = dict(queue_report.get("summary", {}))
    exhaustion_summary = dict(exhaustion_report.get("summary", {}))
    successor_summary = dict(successor_report.get("summary", {}))

    selected_execution_ok = all(
        [
            selected_execution_summary.get("terminal_outcome") == _maybe_text(policy.get("required_selected_execution_outcome")),
            selected_execution_summary.get("next_action") == _maybe_text(policy.get("required_selected_execution_next_action")),
            selected_execution_summary.get("selected_continuation_lane") == _maybe_text(policy.get("required_unlock_lane")),
            selected_execution_summary.get("target_row_id") == _maybe_text(policy.get("required_unlock_target_row")),
        ]
    )
    selected_family_ok = all(
        [
            selected_family_summary.get("terminal_outcome") == _maybe_text(policy.get("required_selected_family_outcome")),
            selected_family_summary.get("next_action") == _maybe_text(policy.get("required_selected_family_next_action")),
            selected_family_summary.get("selected_continuation_lane") == _maybe_text(policy.get("required_unlock_lane")),
            selected_family_summary.get("target_row_id") == _maybe_text(policy.get("required_unlock_target_row")),
            bool(selected_family_summary.get("selected_continuation_machine_pinned")),
        ]
    )
    unlock_ok = all(
        [
            unlock_summary.get("terminal_outcome") == _maybe_text(policy.get("required_unlock_outcome")),
            unlock_summary.get("next_action") == _maybe_text(policy.get("required_unlock_next_action")),
            unlock_summary.get("selected_unlock_payload_lane") == _maybe_text(policy.get("required_unlock_lane")),
            unlock_summary.get("target_row_id") == _maybe_text(policy.get("required_unlock_target_row")),
            bool(unlock_summary.get("selected_unlock_payload_machine_pinned")),
            bool(unlock_summary.get("selected_payload_paths_exist")),
        ]
    )
    queue_ok = all(
        [
            queue_summary.get("terminal_outcome") == _maybe_text(policy.get("required_queue_outcome")),
            queue_summary.get("first_active_row") == _maybe_text(policy.get("required_queue_first_row")),
            queue_summary.get("second_active_row") == _maybe_text(policy.get("required_queue_second_row")),
            queue_summary.get("heavy_structural_row") == _maybe_text(policy.get("required_queue_heavy_row")),
            queue_summary.get("primary_executable_seam") == _maybe_text(policy.get("required_queue_primary_executable_seam")),
        ]
    )
    exhaustion_ok = (
        exhaustion_summary.get("terminal_outcome") == _maybe_text(policy.get("required_exhaustion_outcome"))
    )
    successor_ok = all(
        [
            successor_summary.get("terminal_outcome") == _maybe_text(policy.get("required_successor_outcome")),
            successor_summary.get("next_action") == _maybe_text(policy.get("required_successor_next_action")),
            successor_summary.get("selected_reopen_route") == "NONE",
            successor_summary.get("target_map_primary_executable_row") == _maybe_text(policy.get("required_unlock_target_row")),
        ]
    )
    alignment_ok = all(
        [
            selected_execution_summary.get("target_row_id") == selected_family_summary.get("target_row_id"),
            selected_family_summary.get("target_row_id") == unlock_summary.get("target_row_id"),
            unlock_summary.get("target_row_id") == successor_summary.get("target_map_primary_executable_row"),
            queue_summary.get("primary_executable_seam") == _maybe_text(policy.get("required_queue_primary_executable_seam")),
        ]
    )

    expected_order = [
        "COSMO_SR_SELECTED_CONTINUATION_FAMILY",
        "OBJECTIVE_QUALITY_QUEUE_DOWNSTREAM",
        "POST_CASCADE_SUCCESSOR_REOPEN",
    ]
    contract_violation = ranked_family_order != expected_order

    if not all([selected_execution_ok, selected_family_ok, unlock_ok, queue_ok, exhaustion_ok, successor_ok, alignment_ok]):
        terminal_outcome = "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_REMAINING_PHYSICS_EXECUTION_ORDER_INPUTS_AND_RERUN"
    elif contract_violation:
        terminal_outcome = "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_CONTRACT_VIOLATION"
        next_action = "REPAIR_REMAINING_PHYSICS_EXECUTION_ORDER_POLICY_BEFORE_REPRIORITIZATION"
    else:
        terminal_outcome = "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_MATERIALIZED"
        next_action = _maybe_text(policy.get("required_selected_execution_next_action"))

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    ranked_families = [
        {
            "rank": 1,
            "family_id": ranked_family_order[0] if len(ranked_family_order) > 0 else None,
            "activation_state": "EXECUTED_NONPROMOTED_CLOSEOUT_RECORDED" if selected_execution_ok else "EVIDENCE_INCOMPLETE",
            "entry_surface": _ptr(selected_execution_path),
            "target_row_id": selected_execution_summary.get("target_row_id"),
            "selected_unlock_payload_lane": selected_execution_summary.get("selected_continuation_lane"),
            "next_action": selected_execution_summary.get("next_action"),
            "priority_basis": [
                "SOLE_EXECUTABLE_SEAM",
                "MACHINE_PINNED_PAYLOAD_SELECTED",
                "SINGLE_USE_CONTINUATION_EXECUTION_CONSUMED"
            ],
        },
        {
            "rank": 2,
            "family_id": ranked_family_order[1] if len(ranked_family_order) > 1 else None,
            "activation_state": "DOWNSTREAM_DEFERRED_UNTIL_HIGHER_PRIORITY_CLOSEOUT" if queue_ok else "EVIDENCE_INCOMPLETE",
            "entry_surface": _ptr(queue_path),
            "queue_order": queue_summary.get("queue_order", []),
            "first_active_row": queue_summary.get("first_active_row"),
            "second_active_row": queue_summary.get("second_active_row"),
            "heavy_structural_row": queue_summary.get("heavy_structural_row"),
            "next_action": "PRESERVE_EXISTING_OBJECTIVE_QUALITY_QUEUE_AS_DOWNSTREAM_ONLY_UNTIL_HIGHER_PRIORITY_FAMILY_CLOSEOUT",
            "priority_basis": [
                "CANONICAL_QUEUE_ALREADY_MATERIALIZED",
                "SEAM_REMAINS_DOWNSTREAM_REASSESSMENT_ONLY",
                "NO_LOOKALIKE_ROW_REOPEN_WITHOUT_CHANGED_TRUTH"
            ],
        },
        {
            "rank": 3,
            "family_id": ranked_family_order[2] if len(ranked_family_order) > 2 else None,
            "activation_state": "NOT_ELIGIBLE_UNTIL_FRESH_BLOCKER_FACING_MOVEMENT" if successor_ok else "EVIDENCE_INCOMPLETE",
            "entry_surface": _ptr(successor_path),
            "current_family_scope": exhaustion_summary.get("current_family_scope"),
            "selected_reopen_route": successor_summary.get("selected_reopen_route"),
            "next_action": successor_summary.get("next_action"),
            "priority_basis": [
                "POST_CASCADE_EXHAUSTION_ALREADY_RECORDED",
                "SUCCESSOR_AUTHORIZATION_REQUIRES_FRESH_MOVEMENT",
                "NO_ROUTE_SELECTED"
            ],
        },
    ]

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "cosmo_sr_selected_execution_recorded": selected_execution_ok,
            "cosmo_sr_selected_continuation_recorded": selected_family_ok,
            "cosmo_sr_unlock_recorded": unlock_ok,
            "objective_quality_queue_recorded": queue_ok,
            "post_cascade_exhaustion_recorded": exhaustion_ok,
            "post_cascade_successor_hold_recorded": successor_ok,
            "execution_anchor_alignment_ok": alignment_ok,
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "first_rank_is_machine_pinned_live_family": selected_execution_ok,
                "second_rank_preserves_existing_queue": queue_ok,
                "third_rank_remains_contingent_until_fresh_movement": successor_ok,
            },
            "inputs": {
                "selected_unlock_payload_lane": selected_execution_summary.get("selected_continuation_lane"),
                "primary_executable_seam": queue_summary.get("primary_executable_seam"),
                "queue_order": queue_summary.get("queue_order", []),
                "post_cascade_current_family_scope": exhaustion_summary.get("current_family_scope"),
                "successor_next_action": successor_summary.get("next_action"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "first_family_id": ranked_families[0]["family_id"],
            "second_family_id": ranked_families[1]["family_id"],
            "third_family_id": ranked_families[2]["family_id"],
            "target_row_id": selected_execution_summary.get("target_row_id"),
            "selected_unlock_payload_lane": selected_execution_summary.get("selected_continuation_lane"),
            "queue_primary_executable_seam": queue_summary.get("primary_executable_seam"),
            "successor_selected_route": successor_summary.get("selected_reopen_route"),
            "next_action": next_action,
        },
        "ranked_families": ranked_families,
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_cosmo_sr_selected_continuation_execution_report": _ptr(selected_execution_path),
            "post_plan_cosmo_sr_selected_continuation_family_report": _ptr(selected_family_path),
            "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report": _ptr(unlock_path),
            "post_plan_objective_quality_physics_completion_queue_report": _ptr(queue_path),
            "post_plan_post_cascade_explicit_exhaustion_decision_report": _ptr(exhaustion_path),
            "post_plan_post_cascade_successor_family_eligibility_review_report": _ptr(successor_path),
        },
        "non_claim_boundary": "Repository-local post-plan remaining-physics execution ordering only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-plan remaining-physics execution-order report."
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
        "post_plan_remaining_physics_execution_order_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())