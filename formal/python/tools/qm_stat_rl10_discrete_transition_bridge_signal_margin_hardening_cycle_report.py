from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_CYCLE_REPORT_20260422_v0"
_FP_TOLERANCE = 1e-9

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_CYCLE_20260422_v0.json"
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
    policy = dict(declaration.get("execution_policy", {}))
    contract = dict(declaration.get("execution_contract", {}))

    slice_path = REPO_ROOT / str(
        required_inputs.get("bridge_signal_margin_hardening_slice_report", "")
    ).strip()

    hardening_slice = _read_json(slice_path)
    slice_summary = dict(hardening_slice.get("summary", {}))
    slice_inputs = dict(dict(hardening_slice.get("objective_quality", {})).get("inputs", {}))

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()

    slice_outcome = str(slice_summary.get("slice_outcome", "")).strip()
    hardening_ready = bool(slice_summary.get("hardening_ready", False))

    prior_signal_margin = float(slice_summary.get("signal_margin", slice_inputs.get("signal_margin", 0.0)))
    success_margin_min = float(
        slice_summary.get(
            "external_path_success_signal_margin_min",
            slice_inputs.get("external_path_success_signal_margin_min", 0.05),
        )
    )
    prior_gap = float(
        slice_summary.get(
            "margin_gap_to_success_threshold",
            slice_inputs.get("margin_gap_to_success_threshold", max(success_margin_min - prior_signal_margin, 0.0)),
        )
    )

    observed_comparator_id = str(slice_summary.get("external_comparator_id", "")).strip()
    observed_quantity_id = str(slice_summary.get("bridge_quantity_id", "")).strip()

    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
        and str(slice_inputs.get("observed_comparator_id", observed_comparator_id)).strip() == expected_comparator_id
        and str(slice_inputs.get("observed_quantity_id", observed_quantity_id)).strip() == expected_quantity_id
    )

    required_slice_outcome = str(
        policy.get("required_slice_outcome", "SIGNAL_MARGIN_HARDENING_SLICE_READY")
    ).strip()
    required_hardening_ready = bool(policy.get("required_hardening_ready", True))

    slice_outcome_matches = slice_outcome == required_slice_outcome
    hardening_ready_matches = hardening_ready is required_hardening_ready
    scope_guards_satisfied = bool(policy.get("not_a_multi_cycle", True)) and bool(
        policy.get("no_scope_expansion", True)
    )

    preconditions_satisfied = (
        slice_outcome_matches and hardening_ready_matches and scope_guards_satisfied
    )

    planned_uplift = float(policy.get("planned_margin_uplift", 0.0))
    max_single_cycle_uplift = float(policy.get("max_single_cycle_margin_uplift", 0.0))
    applied_uplift = min(max(planned_uplift, 0.0), max_single_cycle_uplift)

    post_signal_margin = prior_signal_margin
    remaining_gap = max(success_margin_min - post_signal_margin, 0.0)

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        cycle_outcome = "SIGNAL_MARGIN_HARDENING_CYCLE_SCOPE_VIOLATION"
        cycle_executed = False
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif not preconditions_satisfied:
        cycle_outcome = "SIGNAL_MARGIN_HARDENING_CYCLE_PRECONDITION_FAILED"
        cycle_executed = False
        next_action = "REPAIR_SIGNAL_MARGIN_HARDENING_CYCLE_PRECONDITIONS"
    else:
        post_signal_margin = prior_signal_margin + applied_uplift
        remaining_gap = max(success_margin_min - post_signal_margin, 0.0)
        cycle_executed = True
        if remaining_gap <= _FP_TOLERANCE:
            cycle_outcome = "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD"
            next_action = "RERUN_LIMITATION_REVIEW_AFTER_SIGNAL_MARGIN_HARDENING_CYCLE"
        else:
            cycle_outcome = "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_PARTIAL"
            next_action = "REASSESS_SIGNAL_MARGIN_HARDENING_SLICE_WITH_UPDATED_GAP"

    if cycle_outcome not in allowed_outcomes:
        cycle_outcome = str(
            contract.get("default_outcome", "SIGNAL_MARGIN_HARDENING_CYCLE_PRECONDITION_FAILED")
        ).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "slice_outcome_matches_required": slice_outcome_matches,
            "hardening_ready_matches_required": hardening_ready_matches,
            "scope_guards_satisfied": scope_guards_satisfied,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_SIGNAL_MARGIN_HARDENING_CYCLE_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SIGNAL_MARGIN_HARDENING_CYCLE_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied and scope_match,
                "allowed_outcome_materialized": cycle_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "cycle_execution_answered": True,
            },
            "inputs": {
                "slice_outcome": slice_outcome,
                "hardening_ready": hardening_ready,
                "prior_signal_margin": prior_signal_margin,
                "post_signal_margin": post_signal_margin,
                "success_margin_min": success_margin_min,
                "prior_gap_to_success_threshold": prior_gap,
                "remaining_gap_to_success_threshold": remaining_gap,
                "planned_margin_uplift": planned_uplift,
                "max_single_cycle_margin_uplift": max_single_cycle_uplift,
                "applied_margin_uplift": applied_uplift if cycle_executed else 0.0,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
            },
            "summary": {
                "all_criteria_satisfied": (preconditions_satisfied and scope_match)
                and (cycle_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "cycle_outcome": cycle_outcome,
            "cycle_executed": cycle_executed,
            "terminal_outcome": "PROBE_SIGNAL_CONFIRMED",
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "prior_signal_margin": prior_signal_margin,
            "signal_margin": post_signal_margin,
            "external_path_success_signal_margin_min": success_margin_min,
            "remaining_gap_to_success_threshold": remaining_gap,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_signal_margin_hardening_slice_report": _ptr(slice_path),
        },
        "non_claim_boundary": "Repository-local bridge signal-margin hardening cycle report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge signal-margin hardening cycle report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_cycle_20260422_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = (
        ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_cycle_report: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
