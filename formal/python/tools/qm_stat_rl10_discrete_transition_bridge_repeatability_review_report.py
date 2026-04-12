from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_REVIEW_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_REVIEW_20260412_v0.json"
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
    policy = dict(declaration.get("repeatability_policy", {}))
    contract = dict(declaration.get("review_contract", {}))

    limitation_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_limitation_review_report", "")
    ).strip()
    limitation_review = _read_json(limitation_review_path)
    limitation_summary = dict(limitation_review.get("summary", {}))

    limitation_review_outcome = str(limitation_summary.get("review_outcome", "")).strip()
    limitation_primary_cause = str(limitation_summary.get("limitation_primary_cause", "")).strip()
    local_and_refinable = bool(limitation_summary.get("local_and_refinable", False))
    one_more_cycle_justified = bool(
        limitation_summary.get("one_more_bounded_comparator_cycle_justified", False)
    )
    observed_comparator_id = str(limitation_summary.get("external_comparator_id", "")).strip()
    observed_quantity_id = str(limitation_summary.get("bridge_quantity_id", "")).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
    )

    required_limitation_cause = str(policy.get("required_limitation_cause", "")).strip()
    required_local_and_refinable = bool(policy.get("required_local_and_refinable", True))
    repeatability_check_named = bool(policy.get("repeatability_check_named", False))
    cross_probe_check_named = bool(policy.get("cross_probe_consistency_check_named", False))
    path_falsification_observed = bool(policy.get("path_falsification_observed", False))

    limitation_cause_matches = limitation_primary_cause == required_limitation_cause
    local_refinable_confirmed = local_and_refinable == required_local_and_refinable

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(contract.get("default_outcome", "LIMITED_HOLD_RETAINED")).strip()

    if path_falsification_observed or limitation_review_outcome == "LIMITATION_INTERPRETATION_SCOPE_HOLD":
        review_outcome = "PATH_FALSIFIED"
        missing_repeatability_evidence = "path_falsified_or_scope_invalid_no_repeatability_check_relevant"
        bounded_check_possible_without_full_cycle = False
        review_next_action = "RETIRE_CURRENT_SEAM_PATH_AND_RECORD_FALSIFICATION"
    elif (
        limitation_cause_matches
        and local_refinable_confirmed
        and not one_more_cycle_justified
        and scope_match
        and repeatability_check_named
        and not cross_probe_check_named
    ):
        review_outcome = "REPEATABILITY_CHECK_JUSTIFIED"
        missing_repeatability_evidence = "comparator_repeatability_not_confirmed_single_named_check_available"
        bounded_check_possible_without_full_cycle = True
        review_next_action = "EXECUTE_ONE_BOUNDED_REPEATABILITY_CHECK_PACKET"
    elif (
        limitation_cause_matches
        and local_refinable_confirmed
        and not one_more_cycle_justified
        and scope_match
        and cross_probe_check_named
        and not repeatability_check_named
    ):
        review_outcome = "CROSS_PROBE_CONSISTENCY_CHECK_JUSTIFIED"
        missing_repeatability_evidence = "cross_probe_consistency_not_confirmed_single_named_check_available"
        bounded_check_possible_without_full_cycle = True
        review_next_action = "EXECUTE_ONE_BOUNDED_CROSS_PROBE_CONSISTENCY_CHECK_PACKET"
    elif (
        limitation_cause_matches
        and local_refinable_confirmed
        and not one_more_cycle_justified
        and scope_match
        and not repeatability_check_named
        and not cross_probe_check_named
    ):
        # Conservative default: no specific named check has been identified yet
        review_outcome = "LIMITED_HOLD_RETAINED"
        missing_repeatability_evidence = (
            "neither_repeatability_check_nor_cross_probe_consistency_check_has_been_named"
        )
        bounded_check_possible_without_full_cycle = False
        review_next_action = "HOLD_SEAM_AS_LIMITED_UNTIL_ONE_SPECIFIC_BOUNDED_CHECK_IS_NAMED"
    else:
        review_outcome = default_outcome
        missing_repeatability_evidence = (
            "preconditions_unmet_defaulting_to_limited_hold"
        )
        bounded_check_possible_without_full_cycle = False
        review_next_action = "HOLD_SEAM_AS_LIMITED_AND_REVIEW_INCOMING_LIMITATION_DIAGNOSIS"

    if review_outcome not in allowed_outcomes:
        review_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "limitation_cause_matches_expected": limitation_cause_matches,
            "local_and_refinable_confirmed": local_refinable_confirmed,
            "same_comparator_and_quantity_preserved": scope_match,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip() == "EXACTLY_ONE_ALLOWED_REPEATABILITY_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(
                contract.get("no_loop_rule", "")
            ).strip() == "ONE_BRIDGE_REPEATABILITY_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "missing_evidence_named": bool(missing_repeatability_evidence),
            },
            "inputs": {
                "limitation_review_outcome": limitation_review_outcome,
                "limitation_primary_cause": limitation_primary_cause,
                "local_and_refinable": local_and_refinable,
                "one_more_bounded_comparator_cycle_justified": one_more_cycle_justified,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
                "repeatability_check_named": repeatability_check_named,
                "cross_probe_consistency_check_named": cross_probe_check_named,
                "path_falsification_observed": path_falsification_observed,
            },
            "summary": {
                "all_criteria_satisfied": review_outcome
                in {
                    "REPEATABILITY_CHECK_JUSTIFIED",
                    "CROSS_PROBE_CONSISTENCY_CHECK_JUSTIFIED",
                    "LIMITED_HOLD_RETAINED",
                },
                "phase_status": "COMPLETE",
                "next_action": review_next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "missing_repeatability_evidence": missing_repeatability_evidence,
            "bounded_check_possible_without_full_cycle": bounded_check_possible_without_full_cycle,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "next_action": review_next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_limitation_review_report": _ptr(limitation_review_path),
        },
        "non_claim_boundary": "Repository-local bridge repeatability review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge repeatability review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_repeatability_review_20260412_v0.json",
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
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "qm_stat_rl10_discrete_transition_bridge_repeatability_review_report: "
        f"review_outcome={payload['summary']['review_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
