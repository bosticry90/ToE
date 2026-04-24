from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_HARDENING_PROBE_EXECUTION_REFRESH_REPORT_20260422_v0"
_FP_TOLERANCE = 1e-9

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_POST_HARDENING_PROBE_EXECUTION_REFRESH_20260422_v0.json"
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
    refresh_policy = dict(declaration.get("refresh_policy", {}))
    contract = dict(declaration.get("refresh_contract", {}))

    cycle_path = REPO_ROOT / str(
        required_inputs.get("bridge_signal_margin_hardening_cycle_report", "")
    ).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("bridge_probe_execution_report", "")).strip()

    cycle = _read_json(cycle_path)
    execution = _read_json(execution_path)

    cycle_summary = dict(cycle.get("summary", {}))
    cycle_inputs = dict(dict(cycle.get("objective_quality", {})).get("inputs", {}))
    execution_summary = dict(execution.get("summary", {}))
    execution_inputs = dict(dict(execution.get("objective_quality", {})).get("inputs", {}))

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()

    cycle_outcome = str(cycle_summary.get("cycle_outcome", "")).strip()
    cycle_executed = bool(cycle_summary.get("cycle_executed", False))

    required_cycle_outcome = str(
        refresh_policy.get(
            "required_cycle_outcome",
            "SIGNAL_MARGIN_HARDENING_CYCLE_EXECUTED_MARGIN_ADVANCED_TO_THRESHOLD",
        )
    ).strip()
    required_cycle_executed = bool(refresh_policy.get("required_cycle_executed", True))

    cycle_outcome_matches = cycle_outcome == required_cycle_outcome
    cycle_executed_matches = cycle_executed is required_cycle_executed

    scope_guards_satisfied = bool(refresh_policy.get("not_a_multi_cycle", True)) and bool(
        refresh_policy.get("no_scope_expansion", True)
    )

    observed_comparator_id = str(execution_summary.get("external_comparator_id", "")).strip()
    observed_quantity_id = str(execution_summary.get("bridge_quantity_id", "")).strip()
    cycle_comparator_id = str(cycle_summary.get("external_comparator_id", "")).strip()
    cycle_quantity_id = str(cycle_summary.get("bridge_quantity_id", "")).strip()

    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
        and cycle_comparator_id == expected_comparator_id
        and cycle_quantity_id == expected_quantity_id
    )

    preconditions_satisfied = (
        cycle_outcome_matches and cycle_executed_matches and scope_guards_satisfied
    )

    prior_signal_margin = float(execution_summary.get("signal_margin", 0.0))
    post_signal_margin = float(
        cycle_summary.get("signal_margin", cycle_inputs.get("post_signal_margin", prior_signal_margin))
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        refresh_outcome = "POST_HARDENING_PROBE_EXECUTION_REFRESH_SCOPE_VIOLATION"
        inputs_changed = False
        materialized_signal_margin = prior_signal_margin
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif not preconditions_satisfied:
        refresh_outcome = "POST_HARDENING_PROBE_EXECUTION_REFRESH_PRECONDITION_FAILED"
        inputs_changed = False
        materialized_signal_margin = prior_signal_margin
        next_action = "REPAIR_POST_HARDENING_REFRESH_PRECONDITIONS"
    elif abs(post_signal_margin - prior_signal_margin) <= _FP_TOLERANCE:
        refresh_outcome = "POST_HARDENING_PROBE_EXECUTION_UNCHANGED"
        inputs_changed = False
        materialized_signal_margin = prior_signal_margin
        next_action = "RERUN_SIGNIFICANCE_AND_LIMITATION_REVIEW_ON_CURRENT_STATE"
    else:
        refresh_outcome = "POST_HARDENING_PROBE_EXECUTION_REFRESHED"
        inputs_changed = True
        materialized_signal_margin = post_signal_margin
        next_action = "RERUN_SIGNIFICANCE_AND_LIMITATION_REVIEW_ON_REFRESHED_MARGIN_STATE"

    if refresh_outcome not in allowed_outcomes:
        refresh_outcome = str(
            contract.get("default_outcome", "POST_HARDENING_PROBE_EXECUTION_REFRESH_PRECONDITION_FAILED")
        ).strip()

    terminal_outcome = str(execution_summary.get("terminal_outcome", "PROBE_SIGNAL_CONFIRMED")).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "cycle_outcome_matches_required": cycle_outcome_matches,
            "cycle_executed_matches_required": cycle_executed_matches,
            "scope_guards_satisfied": scope_guards_satisfied,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_HARDENING_PROBE_EXECUTION_REFRESH_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_POST_HARDENING_PROBE_EXECUTION_REFRESH_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied and scope_match,
                "allowed_outcome_materialized": refresh_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "refresh_answered": True,
            },
            "inputs": {
                "execution_terminal_outcome": terminal_outcome,
                "prior_signal_margin": prior_signal_margin,
                "post_signal_margin": materialized_signal_margin,
                "inputs_changed": inputs_changed,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
                "probe_signal_strength": execution_inputs.get("probe_signal_strength", None),
                "probe_signal_threshold": execution_inputs.get("probe_signal_threshold", None),
                "probe_discrimination_threshold": execution_inputs.get("probe_discrimination_threshold", None),
                "path_falsification_observed": execution_inputs.get("path_falsification_observed", None),
            },
            "summary": {
                "all_criteria_satisfied": (preconditions_satisfied and scope_match)
                and (refresh_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "refresh_outcome": refresh_outcome,
            "terminal_outcome": terminal_outcome,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin": materialized_signal_margin,
            "prior_signal_margin": prior_signal_margin,
            "inputs_changed": inputs_changed,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_signal_margin_hardening_cycle_report": _ptr(cycle_path),
            "bridge_probe_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local bridge post-hardening probe execution refresh report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge post-hardening probe execution refresh report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_post_hardening_probe_execution_refresh_20260422_v0.json",
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
    print(
        "qm_stat_rl10_discrete_transition_bridge_post_hardening_probe_execution_refresh_report: "
        f"{out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
