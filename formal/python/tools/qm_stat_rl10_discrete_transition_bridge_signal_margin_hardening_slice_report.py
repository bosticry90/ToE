from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_SLICE_REPORT_20260422_v0"
_FP_TOLERANCE = 1e-9

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_MARGIN_HARDENING_SLICE_20260422_v0.json"
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
    policy = dict(declaration.get("hardening_policy", {}))
    contract = dict(declaration.get("hardening_contract", {}))

    limitation_path = REPO_ROOT / str(required_inputs.get("bridge_limitation_review_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("bridge_probe_execution_report", "")).strip()

    limitation = _read_json(limitation_path)
    execution = _read_json(execution_path)

    limitation_summary = dict(limitation.get("summary", {}))
    limitation_inputs = dict(dict(limitation.get("objective_quality", {})).get("inputs", {}))
    execution_summary = dict(execution.get("summary", {}))

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()

    limitation_review_outcome = str(limitation_summary.get("review_outcome", "")).strip()
    limitation_primary_cause = str(limitation_summary.get("limitation_primary_cause", "")).strip()

    signal_margin = float(limitation_summary.get("signal_margin", limitation_inputs.get("signal_margin", 0.0)))
    success_margin_min = float(limitation_inputs.get("external_path_success_signal_margin_min", 0.05))
    margin_gap_to_success_threshold = max(success_margin_min - signal_margin, 0.0)

    comparator_repeatability_confirmed = bool(
        limitation_inputs.get("comparator_repeatability_confirmed", False)
    )
    cross_probe_consistency_confirmed = bool(
        limitation_inputs.get("cross_probe_consistency_confirmed", False)
    )

    observed_comparator_id = str(execution_summary.get("external_comparator_id", "")).strip()
    observed_quantity_id = str(execution_summary.get("bridge_quantity_id", "")).strip()

    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
        and str(limitation_summary.get("external_comparator_id", "")).strip() == expected_comparator_id
        and str(limitation_summary.get("bridge_quantity_id", "")).strip() == expected_quantity_id
    )

    required_review_outcome = str(
        policy.get("required_limitation_review_outcome", "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD")
    ).strip()
    required_primary_cause = str(
        policy.get("required_limitation_primary_cause", "signal_margin_below_external_path_success_threshold")
    ).strip()

    require_repeatability = bool(policy.get("require_comparator_repeatability_confirmed", True))
    require_cross_probe = bool(policy.get("require_cross_probe_consistency_confirmed", True))

    review_outcome_matches = limitation_review_outcome == required_review_outcome
    primary_cause_matches = limitation_primary_cause == required_primary_cause
    repeatability_matches = comparator_repeatability_confirmed if require_repeatability else True
    cross_probe_matches = cross_probe_consistency_confirmed if require_cross_probe else True
    scope_guards_satisfied = bool(policy.get("not_a_new_comparator_cycle", True)) and bool(
        policy.get("no_scope_expansion", True)
    )

    preconditions_satisfied = (
        review_outcome_matches
        and primary_cause_matches
        and repeatability_matches
        and cross_probe_matches
        and scope_guards_satisfied
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        slice_outcome = "SIGNAL_MARGIN_HARDENING_SLICE_SCOPE_VIOLATION"
        hardening_ready = False
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif not preconditions_satisfied:
        slice_outcome = "SIGNAL_MARGIN_HARDENING_SLICE_PRECONDITION_FAILED"
        hardening_ready = False
        next_action = "REPAIR_SIGNAL_MARGIN_HARDENING_PRECONDITIONS"
    elif margin_gap_to_success_threshold <= _FP_TOLERANCE:
        slice_outcome = "SIGNAL_MARGIN_HARDENING_SLICE_NOT_REQUIRED"
        hardening_ready = False
        next_action = "KEEP_SEAM_ACTIVE_AND_VERIFY_LIMITATION_STATE_STABILITY"
    else:
        slice_outcome = "SIGNAL_MARGIN_HARDENING_SLICE_READY"
        hardening_ready = True
        next_action = "EXECUTE_ONE_BOUNDED_SIGNAL_MARGIN_HARDENING_CYCLE"

    if slice_outcome not in allowed_outcomes:
        slice_outcome = str(
            contract.get("default_outcome", "SIGNAL_MARGIN_HARDENING_SLICE_PRECONDITION_FAILED")
        ).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "limitation_review_outcome_matches_required": review_outcome_matches,
            "limitation_primary_cause_matches_required": primary_cause_matches,
            "comparator_repeatability_confirmed_matches_required": repeatability_matches,
            "cross_probe_consistency_confirmed_matches_required": cross_probe_matches,
            "scope_guards_satisfied": scope_guards_satisfied,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_SIGNAL_MARGIN_HARDENING_SLICE_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SIGNAL_MARGIN_HARDENING_SLICE_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied and scope_match,
                "allowed_outcome_materialized": slice_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "hardening_readiness_answered": True,
            },
            "inputs": {
                "limitation_review_outcome": limitation_review_outcome,
                "limitation_primary_cause": limitation_primary_cause,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": success_margin_min,
                "margin_gap_to_success_threshold": margin_gap_to_success_threshold,
                "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
            },
            "summary": {
                "all_criteria_satisfied": (preconditions_satisfied and scope_match)
                and (slice_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "slice_outcome": slice_outcome,
            "hardening_ready": hardening_ready,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin": signal_margin,
            "external_path_success_signal_margin_min": success_margin_min,
            "margin_gap_to_success_threshold": margin_gap_to_success_threshold,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_limitation_review_report": _ptr(limitation_path),
            "bridge_probe_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local bridge signal-margin hardening slice report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge signal-margin hardening slice report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_slice_20260422_v0.json",
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
    print(f"qm_stat_rl10_discrete_transition_bridge_signal_margin_hardening_slice_report: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
