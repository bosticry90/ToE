from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_COMPARATOR_REPEATABILITY_CONFIRMATION_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_COMPARATOR_REPEATABILITY_CONFIRMATION_20260422_v0.json"
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

    char_path = REPO_ROOT / str(
        required_inputs.get("bridge_limitation_characterization_packet_report", "")
    ).strip()
    naming_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_check_naming_review_report", "")
    ).strip()
    admissibility_path = REPO_ROOT / str(
        required_inputs.get("bridge_material_repeatability_admissibility_criteria_report", "")
    ).strip()

    char_report = _read_json(char_path)
    naming_review = _read_json(naming_review_path)
    admissibility = _read_json(admissibility_path)

    char_summary = dict(char_report.get("summary", {}))
    naming_summary = dict(naming_review.get("summary", {}))
    admissibility_summary = dict(admissibility.get("summary", {}))

    limitation_class_outcome = str(char_summary.get("packet_outcome", "")).strip()
    naming_review_outcome = str(naming_summary.get("review_outcome", "")).strip()
    proposed_check_kind = str(naming_summary.get("proposed_check_kind", "")).strip()
    proposed_check_name = str(naming_summary.get("proposed_check_name", "")).strip()
    admissibility_outcome = str(admissibility_summary.get("terminal_outcome", "")).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    expected_check_id = str(seam_scope.get("named_check_id", "")).strip()

    required_limitation_class = str(policy.get("required_limitation_class", "")).strip()
    required_naming_outcome = str(policy.get("required_naming_review_outcome", "")).strip()
    required_check_kind = str(policy.get("required_proposed_check_kind", "")).strip()
    required_admissibility_outcome = str(
        policy.get("required_admissibility_criteria_outcome", "")
    ).strip()
    window_check_executed = bool(policy.get("window_check_executed", False))
    window_check_comparator_stable = bool(policy.get("window_check_comparator_stable", False))
    window_check_within_admissible_scope = bool(
        policy.get("window_check_within_admissible_scope", True)
    )
    not_a_full_second_cycle = bool(policy.get("not_a_full_second_cycle", True))
    no_scope_expansion = bool(policy.get("no_scope_expansion", True))
    signal_margin_gap_targeted = float(policy.get("signal_margin_gap_targeted", 0.01))
    signal_margin_threshold = float(policy.get("signal_margin_threshold", 0.05))

    # Precondition checks
    limitation_class_matches = limitation_class_outcome == required_limitation_class
    naming_outcome_matches = naming_review_outcome == required_naming_outcome
    check_kind_matches = proposed_check_kind == required_check_kind
    check_name_matches = proposed_check_name == expected_check_id
    admissibility_matches = admissibility_outcome == required_admissibility_outcome
    scope_guards_satisfied = not_a_full_second_cycle and no_scope_expansion

    admissibility_preconditions_satisfied = (
        limitation_class_matches
        and naming_outcome_matches
        and check_kind_matches
        and check_name_matches
        and admissibility_matches
        and scope_guards_satisfied
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not admissibility_preconditions_satisfied:
        confirmation_outcome = "ADMISSIBILITY_PRECONDITION_FAILED"
        repeatability_confirmed = False
        confirmation_ruling = "PRECONDITIONS_NOT_MET"
        next_action = "REPAIR_ADMISSIBILITY_PRECONDITIONS_BEFORE_WINDOW_CHECK"
    elif not window_check_within_admissible_scope:
        confirmation_outcome = "WINDOW_CHECK_SCOPE_VIOLATION"
        repeatability_confirmed = False
        confirmation_ruling = "SCOPE_VIOLATION_DETECTED"
        next_action = "HOLD_AND_RESTORE_ADMISSIBLE_SCOPE"
    elif window_check_executed and window_check_comparator_stable:
        confirmation_outcome = "COMPARATOR_REPEATABILITY_CONFIRMED"
        repeatability_confirmed = True
        confirmation_ruling = "WINDOW_CHECK_PASSED_COMPARATOR_STABLE"
        next_action = "UPDATE_SIGNIFICANCE_INPUTS_AND_RERUN_LIMITATION_REVIEW"
    else:
        # Default: check named and admissible but not yet confirmed (window not yet executed or
        # comparator not yet shown stable) — honest current state
        confirmation_outcome = "COMPARATOR_REPEATABILITY_NOT_YET_CONFIRMED"
        repeatability_confirmed = False
        confirmation_ruling = "WINDOW_CHECK_NAMED_AND_ADMISSIBLE_BUT_NOT_YET_EXECUTED_OR_STABLE"
        next_action = "EXECUTE_ONE_BOUNDED_WINDOW_CHECK_AGAINST_NAMED_REPEATABILITY_CHECK_ID"

    if confirmation_outcome not in allowed_outcomes:
        confirmation_outcome = str(
            contract.get("default_outcome", "COMPARATOR_REPEATABILITY_NOT_YET_CONFIRMED")
        ).strip()

    all_criteria_satisfied = admissibility_preconditions_satisfied and (
        confirmation_outcome in allowed_outcomes
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "limitation_class_is_comparator_bound": limitation_class_matches,
            "naming_review_outcome_is_bounded_check_named": naming_outcome_matches,
            "check_kind_is_repeatability": check_kind_matches,
            "check_name_matches_seam_scope": check_name_matches,
            "admissibility_criteria_declared": admissibility_matches,
            "scope_guards_satisfied": scope_guards_satisfied,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_COMPARATOR_REPEATABILITY_CONFIRMATION_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_COMPARATOR_REPEATABILITY_CONFIRMATION_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "admissibility_preconditions_satisfied": admissibility_preconditions_satisfied,
                "allowed_outcome_materialized": confirmation_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "all_criteria_satisfied": all_criteria_satisfied,
            },
            "inputs": {
                "limitation_class_outcome": limitation_class_outcome,
                "naming_review_outcome": naming_review_outcome,
                "proposed_check_kind": proposed_check_kind,
                "proposed_check_name": proposed_check_name,
                "admissibility_outcome": admissibility_outcome,
                "window_check_executed": window_check_executed,
                "window_check_comparator_stable": window_check_comparator_stable,
                "window_check_within_admissible_scope": window_check_within_admissible_scope,
                "not_a_full_second_cycle": not_a_full_second_cycle,
                "no_scope_expansion": no_scope_expansion,
                "signal_margin_gap_targeted": signal_margin_gap_targeted,
                "signal_margin_threshold": signal_margin_threshold,
                "expected_comparator_id": expected_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "expected_check_id": expected_check_id,
            },
            "summary": {
                "all_criteria_satisfied": all_criteria_satisfied,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "confirmation_outcome": confirmation_outcome,
            "confirmation_ruling": confirmation_ruling,
            "repeatability_confirmed": repeatability_confirmed,
            "named_check_id": proposed_check_name,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin_gap_targeted": signal_margin_gap_targeted,
            "signal_margin_threshold": signal_margin_threshold,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_limitation_characterization_packet_report": _ptr(char_path),
            "bridge_repeatability_check_naming_review_report": _ptr(naming_review_path),
            "bridge_material_repeatability_admissibility_criteria_report": _ptr(admissibility_path),
        },
        "non_claim_boundary": "Repository-local bridge comparator-repeatability confirmation report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge comparator-repeatability confirmation report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_comparator_repeatability_confirmation_20260422_v0.json",
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
        f"qm_stat_rl10_discrete_transition_bridge_comparator_repeatability_confirmation_report: {out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
