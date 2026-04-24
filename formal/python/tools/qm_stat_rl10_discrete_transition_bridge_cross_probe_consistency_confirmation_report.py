from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_20260422_v0.json"
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
    policy = dict(declaration.get("confirmation_policy", {}))
    contract = dict(declaration.get("confirmation_contract", {}))

    significance_path = REPO_ROOT / str(required_inputs.get("bridge_significance_inputs_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("bridge_probe_execution_report", "")).strip()
    ruling_path = REPO_ROOT / str(required_inputs.get("bridge_probe_ruling_report", "")).strip()

    significance = _read_json(significance_path)
    execution = _read_json(execution_path)
    ruling = _read_json(ruling_path)

    significance_summary = dict(significance.get("summary", {}))
    significance_inputs = dict(dict(significance.get("objective_quality", {})).get("inputs", {}))
    execution_summary = dict(execution.get("summary", {}))
    ruling_summary = dict(ruling.get("summary", {}))

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()

    significance_outcome = str(significance_summary.get("adjudication_outcome", "")).strip()
    execution_terminal_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    ruling_terminal_outcome = str(ruling_summary.get("terminal_outcome", "")).strip()
    ruling_status = str(ruling_summary.get("ruling_status", "")).strip()

    prior_comparator_repeatability_confirmed = bool(
        significance_inputs.get("comparator_repeatability_confirmed", False)
    )
    prior_cross_probe_consistency_confirmed = bool(
        significance_inputs.get("cross_probe_consistency_confirmed", False)
    )

    signal_margin = float(significance_inputs.get("signal_margin", significance_summary.get("signal_margin", 0.0)))
    external_path_success_signal_margin_min = float(
        significance_inputs.get("external_path_success_signal_margin_min", 0.05)
    )
    confirmed_but_limited_signal_margin_min = float(
        significance_inputs.get("confirmed_but_limited_signal_margin_min", 0.02)
    )
    one_more_cycle_signal_margin_min = float(
        significance_inputs.get("one_more_cycle_signal_margin_min", 0.0)
    )

    sig_comparator_id = str(significance_summary.get("external_comparator_id", "")).strip()
    sig_quantity_id = str(significance_summary.get("bridge_quantity_id", "")).strip()
    obs_comparator_id = str(execution_summary.get("external_comparator_id", "")).strip()
    obs_quantity_id = str(execution_summary.get("bridge_quantity_id", "")).strip()

    scope_match = (
        sig_comparator_id == expected_comparator_id
        and sig_quantity_id == expected_quantity_id
        and obs_comparator_id == expected_comparator_id
        and obs_quantity_id == expected_quantity_id
    )

    required_significance_outcome = str(
        policy.get("required_significance_outcome", "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED")
    ).strip()
    required_execution_outcome = str(
        policy.get("required_execution_terminal_outcome", "PROBE_SIGNAL_CONFIRMED")
    ).strip()
    required_ruling_outcome = str(
        policy.get("required_ruling_terminal_outcome", "PROBE_SIGNAL_CONFIRMED")
    ).strip()
    required_ruling_status = str(
        policy.get("required_ruling_status", "TERMINAL_OUTCOME_CONFIRMED")
    ).strip()

    require_repeatability_confirmed = bool(policy.get("require_comparator_repeatability_confirmed", True))
    not_a_new_probe_cycle = bool(policy.get("not_a_new_probe_cycle", True))
    no_scope_expansion = bool(policy.get("no_scope_expansion", True))

    significance_outcome_matches = significance_outcome == required_significance_outcome
    execution_outcome_matches = execution_terminal_outcome == required_execution_outcome
    ruling_outcome_matches = ruling_terminal_outcome == required_ruling_outcome
    ruling_status_matches = ruling_status == required_ruling_status
    repeatability_precondition_matches = (
        prior_comparator_repeatability_confirmed if require_repeatability_confirmed else True
    )
    scope_guards_satisfied = not_a_new_probe_cycle and no_scope_expansion

    core_preconditions_satisfied = (
        significance_outcome_matches
        and execution_outcome_matches
        and ruling_outcome_matches
        and ruling_status_matches
        and repeatability_precondition_matches
        and scope_guards_satisfied
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        confirmation_outcome = "CROSS_PROBE_CONSISTENCY_SCOPE_VIOLATION"
        updated_cross_probe_consistency_confirmed = prior_cross_probe_consistency_confirmed
        inputs_changed = False
        confirmation_ruling = "DECLARED_AND_OBSERVED_SCOPE_MISMATCH"
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif not core_preconditions_satisfied:
        confirmation_outcome = "CROSS_PROBE_CONSISTENCY_PRECONDITION_FAILED"
        updated_cross_probe_consistency_confirmed = prior_cross_probe_consistency_confirmed
        inputs_changed = False
        confirmation_ruling = "PRECONDITIONS_NOT_MET"
        next_action = "REPAIR_CROSS_PROBE_CONSISTENCY_PRECONDITIONS"
    elif prior_cross_probe_consistency_confirmed:
        confirmation_outcome = "CROSS_PROBE_CONSISTENCY_UNCHANGED"
        updated_cross_probe_consistency_confirmed = True
        inputs_changed = False
        confirmation_ruling = "ALREADY_CONFIRMED"
        next_action = "RERUN_LIMITATION_REVIEW_WITH_REFRESHED_SIGNIFICANCE_INPUTS"
    else:
        confirmation_outcome = "CROSS_PROBE_CONSISTENCY_CONFIRMED"
        updated_cross_probe_consistency_confirmed = True
        inputs_changed = True
        confirmation_ruling = "BOUNDED_CROSS_PROBE_CONSISTENCY_CONFIRMED"
        next_action = "RERUN_LIMITATION_REVIEW_WITH_REFRESHED_SIGNIFICANCE_INPUTS"

    if confirmation_outcome not in allowed_outcomes:
        confirmation_outcome = str(
            contract.get("default_outcome", "CROSS_PROBE_CONSISTENCY_UNCHANGED")
        ).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "significance_outcome_matches_required": significance_outcome_matches,
            "execution_outcome_matches_required": execution_outcome_matches,
            "ruling_outcome_matches_required": ruling_outcome_matches,
            "ruling_status_matches_required": ruling_status_matches,
            "comparator_repeatability_precondition_matches": repeatability_precondition_matches,
            "scope_guards_satisfied": scope_guards_satisfied,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_CROSS_PROBE_CONSISTENCY_CONFIRMATION_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_CROSS_PROBE_CONSISTENCY_CONFIRMATION_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": core_preconditions_satisfied and scope_match,
                "allowed_outcome_materialized": confirmation_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "all_criteria_satisfied": (core_preconditions_satisfied and scope_match)
                and (confirmation_outcome in allowed_outcomes),
            },
            # Preserve structure expected by limitation review tool.
            "inputs": {
                "comparator_repeatability_confirmed": prior_comparator_repeatability_confirmed,
                "cross_probe_consistency_confirmed": updated_cross_probe_consistency_confirmed,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": external_path_success_signal_margin_min,
                "confirmed_but_limited_signal_margin_min": confirmed_but_limited_signal_margin_min,
                "one_more_cycle_signal_margin_min": one_more_cycle_signal_margin_min,
                "prior_cross_probe_consistency_confirmed": prior_cross_probe_consistency_confirmed,
                "cross_probe_consistency_confirmation_outcome": confirmation_outcome,
                "expected_comparator_id": expected_comparator_id,
                "expected_quantity_id": expected_quantity_id,
            },
            "summary": {
                "all_criteria_satisfied": (core_preconditions_satisfied and scope_match)
                and (confirmation_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        # Summary mirrors significance adjudication shape so limitation review can consume it.
        "summary": {
            "adjudication_outcome": significance_outcome,
            "confirmation_outcome": confirmation_outcome,
            "confirmation_ruling": confirmation_ruling,
            "inputs_changed": inputs_changed,
            "cross_probe_consistency_confirmed_updated_to": updated_cross_probe_consistency_confirmed,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin": signal_margin,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_significance_inputs_report": _ptr(significance_path),
            "bridge_probe_execution_report": _ptr(execution_path),
            "bridge_probe_ruling_report": _ptr(ruling_path),
        },
        "non_claim_boundary": "Repository-local bridge cross-probe consistency confirmation report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge cross-probe consistency confirmation report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_cross_probe_consistency_confirmation_20260422_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_cross_probe_consistency_confirmation_report: "
        f"{out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
