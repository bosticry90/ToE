from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json"
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
    policy = dict(declaration.get("eligibility_policy", {}))
    contract = dict(declaration.get("eligibility_contract", {}))

    exhaustion_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_post_cascade_explicit_exhaustion_decision_report"))
    blocker_path = REPO_ROOT / _maybe_text(required_inputs.get("blocker_burn_dashboard_report"))
    target_map_path = REPO_ROOT / _maybe_text(required_inputs.get("post_plan_physics_advancement_target_map_report"))

    exhaustion_report = _read_json(exhaustion_path)
    blocker_report = _read_json(blocker_path)
    target_map_report = _read_json(target_map_path)

    required_exhaustion_outcome = _maybe_text(policy.get("required_exhaustion_outcome"))
    required_successor_declared = bool(policy.get("required_successor_declared", False))
    selected_reopen_route = _maybe_text(policy.get("selected_reopen_route")) or "NONE"
    selected_reopen_route_class = _maybe_text(policy.get("selected_reopen_route_class"))
    selected_reopen_route_family_declaration = _maybe_text(policy.get("selected_reopen_route_family_declaration"))
    selected_reopen_route_family_gate = _maybe_text(policy.get("selected_reopen_route_family_gate"))
    selected_reopen_route_machine_pinned = bool(policy.get("selected_reopen_route_machine_pinned", False))

    exhaustion_ok = exhaustion_report.get("summary", {}).get("terminal_outcome") == required_exhaustion_outcome
    successor_declared = bool(exhaustion_report.get("summary", {}).get("successor_declared"))
    successor_state_ok = successor_declared == required_successor_declared

    blocker_deltas = blocker_report.get("blocker_scoreboard", {}).get("delta_by_class", {})
    fresh_theorem_gap_movement = int(blocker_deltas.get("THEOREM_GAP", 0)) < 0
    fresh_seam_integration_movement = int(blocker_deltas.get("SEAM_INTEGRATION_GAP", 0)) < 0
    fresh_blocker_facing_movement = fresh_theorem_gap_movement or fresh_seam_integration_movement

    routed_rows = target_map_report.get("routed_rows", [])
    selected_route_visible = any(row.get("row_id") == selected_reopen_route for row in routed_rows)
    target_map_primary_row = next(
        (row.get("row_id") for row in routed_rows if row.get("route_class") == "EXECUTABLE_NOW"),
        None,
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = _maybe_text(contract.get("default_outcome"))

    contract_violation = False
    if selected_reopen_route == "NONE":
        contract_violation = any(
            [
                selected_reopen_route_class,
                selected_reopen_route_family_declaration,
                selected_reopen_route_family_gate,
                selected_reopen_route_machine_pinned,
            ]
        )
    else:
        contract_violation = not all(
            [
                selected_reopen_route_class,
                selected_reopen_route_family_declaration,
                selected_reopen_route_family_gate,
                selected_reopen_route_machine_pinned,
                selected_route_visible,
                fresh_blocker_facing_movement,
            ]
        )

    if not all([exhaustion_report, blocker_report, target_map_report]):
        terminal_outcome = "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_INPUTS_AND_RERUN"
    elif not all([exhaustion_ok, successor_state_ok]):
        terminal_outcome = "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_POST_CASCADE_EXHAUSTION_STATE_AND_RERUN_ELIGIBILITY_REVIEW"
    elif contract_violation:
        terminal_outcome = "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_CONTRACT_VIOLATION"
        next_action = "REPAIR_SUCCESSOR_ELIGIBILITY_POLICY_BEFORE_ANY_REOPEN_AUTHORIZATION"
    elif fresh_blocker_facing_movement and selected_reopen_route != "NONE":
        terminal_outcome = "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_ONE_ROUTE_AUTHORIZED"
        next_action = "AUTHOR_AND_EXECUTE_DECLARED_SUCCESSOR_FAMILY_ONCE"
    else:
        terminal_outcome = "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE"
        next_action = "ACCEPT_TERMINAL_EXHAUSTION_READ_UNTIL_FRESH_BLOCKER_FACING_MOVEMENT_IS_MACHINE_PINNED"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "exhausted_current_family_recorded": exhaustion_ok,
            "required_successor_declared_state_recorded": successor_state_ok,
            "fresh_theorem_gap_movement_recorded": fresh_theorem_gap_movement,
            "fresh_seam_integration_movement_recorded": fresh_seam_integration_movement,
            "selected_reopen_route_visible_in_target_map": selected_route_visible or selected_reopen_route == "NONE",
            "single_terminal_outcome_rule_declared": _maybe_text(contract.get("single_terminal_outcome_rule"))
            == "EXACTLY_ONE_ALLOWED_POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_OUTCOME",
            "no_loop_rule_declared": _maybe_text(contract.get("no_loop_rule"))
            == "ONE_POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_REVIEW_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "authorization_requires_fresh_blocker_facing_movement": (
                    terminal_outcome != "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_ONE_ROUTE_AUTHORIZED"
                )
                or fresh_blocker_facing_movement,
                "authorization_requires_machine_pinned_selected_route": (
                    terminal_outcome != "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_ONE_ROUTE_AUTHORIZED"
                )
                or all([
                    selected_reopen_route != "NONE",
                    selected_reopen_route_machine_pinned,
                    selected_route_visible,
                ]),
            },
            "inputs": {
                "exhaustion_terminal_outcome": exhaustion_report.get("summary", {}).get("terminal_outcome"),
                "exhaustion_next_action": exhaustion_report.get("summary", {}).get("next_action"),
                "successor_declared": successor_declared,
                "theorem_gap_delta": blocker_deltas.get("THEOREM_GAP", 0),
                "seam_integration_gap_delta": blocker_deltas.get("SEAM_INTEGRATION_GAP", 0),
                "target_map_primary_executable_row": target_map_primary_row,
                "selected_reopen_route": selected_reopen_route,
                "selected_reopen_route_class": selected_reopen_route_class,
                "selected_reopen_route_machine_pinned": selected_reopen_route_machine_pinned,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "current_family_scope": exhaustion_report.get("summary", {}).get("current_family_scope"),
            "fresh_blocker_facing_movement": fresh_blocker_facing_movement,
            "selected_reopen_route": selected_reopen_route,
            "selected_reopen_route_class": selected_reopen_route_class or None,
            "target_map_primary_executable_row": target_map_primary_row,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "post_plan_post_cascade_explicit_exhaustion_decision_report": _ptr(exhaustion_path),
            "blocker_burn_dashboard_report": _ptr(blocker_path),
            "post_plan_physics_advancement_target_map_report": _ptr(target_map_path),
            "selected_reopen_route_family_declaration": selected_reopen_route_family_declaration or None,
            "selected_reopen_route_family_gate": selected_reopen_route_family_gate or None,
        },
        "non_claim_boundary": "Repository-local post-cascade successor-family eligibility review only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-plan post-cascade successor-family eligibility review report."
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
        "post_plan_post_cascade_successor_family_eligibility_review_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the post-plan post-cascade successor-family eligibility review report."
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
        "post_plan_post_cascade_successor_family_eligibility_review_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())