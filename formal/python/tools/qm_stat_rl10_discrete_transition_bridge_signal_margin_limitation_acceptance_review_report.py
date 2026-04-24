from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_20260422_v0.json"
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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    seam_scope = dict(declaration.get("seam_scope", {}))
    policy = dict(declaration.get("acceptance_policy", {}))
    contract = dict(declaration.get("acceptance_contract", {}))

    cycle_path = REPO_ROOT / str(
        required_inputs.get("bridge_signal_margin_hardening_cycle_report", "")
    ).strip()
    limitation_path = REPO_ROOT / str(required_inputs.get("bridge_limitation_review_report", "")).strip()

    cycle = _read_json(cycle_path)
    limitation = _read_json(limitation_path)

    cycle_summary = dict(cycle.get("summary", {}))
    cycle_inputs = dict(dict(cycle.get("objective_quality", {})).get("inputs", {}))
    limitation_summary = dict(limitation.get("summary", {}))
    limitation_inputs = dict(dict(limitation.get("objective_quality", {})).get("inputs", {}))

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()

    cycle_outcome = str(cycle_summary.get("cycle_outcome", "")).strip()
    limitation_outcome = str(limitation_summary.get("review_outcome", "")).strip()
    limitation_primary_cause = str(limitation_summary.get("limitation_primary_cause", "")).strip()

    required_cycle_outcome = str(
        policy.get("required_cycle_outcome", "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD")
    ).strip()
    required_limitation_outcome = str(
        policy.get("required_limitation_outcome", "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD")
    ).strip()
    required_primary_cause = str(
        policy.get("required_limitation_primary_cause", "signal_margin_below_external_path_success_threshold")
    ).strip()

    tolerance = float(policy.get("margin_ceiling_tolerance", 1e-9))

    cycle_outcome_matches = cycle_outcome == required_cycle_outcome
    limitation_outcome_matches = limitation_outcome == required_limitation_outcome
    limitation_primary_cause_matches = limitation_primary_cause == required_primary_cause
    scope_guards_satisfied = bool(policy.get("not_a_multi_cycle", True)) and bool(
        policy.get("no_scope_expansion", True)
    )

    cycle_comparator_id = str(cycle_summary.get("external_comparator_id", "")).strip()
    cycle_quantity_id = str(cycle_summary.get("bridge_quantity_id", "")).strip()
    limitation_comparator_id = str(limitation_summary.get("external_comparator_id", "")).strip()
    limitation_quantity_id = str(limitation_summary.get("bridge_quantity_id", "")).strip()

    scope_match = (
        cycle_comparator_id == expected_comparator_id
        and cycle_quantity_id == expected_quantity_id
        and limitation_comparator_id == expected_comparator_id
        and limitation_quantity_id == expected_quantity_id
    )

    preconditions_satisfied = (
        cycle_outcome_matches
        and limitation_outcome_matches
        and limitation_primary_cause_matches
        and scope_guards_satisfied
    )

    post_signal_margin = float(cycle_summary.get("signal_margin", cycle_inputs.get("post_signal_margin", 0.0)))
    success_margin_min = float(
        cycle_summary.get("external_path_success_signal_margin_min", cycle_inputs.get("success_margin_min", 0.05))
    )
    remaining_gap = max(success_margin_min - post_signal_margin, 0.0)

    allow_acceptance_at_current_ceiling = bool(
        policy.get("allow_acceptance_at_current_margin_ceiling", True)
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        review_outcome = "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_SCOPE_VIOLATION"
        accepted_as_margin_limited = False
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif not preconditions_satisfied:
        review_outcome = "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITION_FAILED"
        accepted_as_margin_limited = False
        next_action = "REPAIR_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITIONS"
    elif allow_acceptance_at_current_ceiling and remaining_gap <= tolerance:
        review_outcome = "SIGNAL_MARGIN_LIMITATION_ACCEPTED_AT_CURRENT_CEILING"
        accepted_as_margin_limited = True
        next_action = "KEEP_SEAM_PRIMARY_MARGIN_LIMITED_AND_RECORD_ACCEPTANCE_BOUNDARY"
    else:
        review_outcome = "SIGNAL_MARGIN_LIMITATION_NOT_ACCEPTED_CONTINUE_BOUNDED_HARDENING"
        accepted_as_margin_limited = False
        next_action = "AUTHOR_ONE_ADDITIONAL_BOUNDED_SIGNAL_MARGIN_HARDENING_CYCLE"

    if review_outcome not in allowed_outcomes:
        review_outcome = str(
            contract.get("default_outcome", "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITION_FAILED")
        ).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "cycle_outcome_matches_required": cycle_outcome_matches,
            "limitation_outcome_matches_required": limitation_outcome_matches,
            "limitation_primary_cause_matches_required": limitation_primary_cause_matches,
            "scope_guards_satisfied": scope_guards_satisfied,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_REVIEW_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied and scope_match,
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "acceptance_answered": True,
            },
            "inputs": {
                "cycle_outcome": cycle_outcome,
                "limitation_outcome": limitation_outcome,
                "limitation_primary_cause": limitation_primary_cause,
                "post_signal_margin": post_signal_margin,
                "external_path_success_signal_margin_min": success_margin_min,
                "remaining_gap_to_success_threshold": remaining_gap,
                "expected_comparator_id": expected_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_cycle_comparator_id": cycle_comparator_id,
                "observed_cycle_quantity_id": cycle_quantity_id,
                "observed_limitation_comparator_id": limitation_comparator_id,
                "observed_limitation_quantity_id": limitation_quantity_id,
            },
            "summary": {
                "all_criteria_satisfied": (preconditions_satisfied and scope_match)
                and (review_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "accepted_as_margin_limited": accepted_as_margin_limited,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin": post_signal_margin,
            "external_path_success_signal_margin_min": success_margin_min,
            "remaining_gap_to_success_threshold": remaining_gap,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_signal_margin_hardening_cycle_report": _ptr(cycle_path),
            "bridge_limitation_review_report": _ptr(limitation_path),
        },
        "non_claim_boundary": "Repository-local bridge signal-margin limitation acceptance review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge signal-margin limitation acceptance review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_20260422_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        "qm_stat_rl10_discrete_transition_bridge_signal_margin_limitation_acceptance_review_report: "
        f"{out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
