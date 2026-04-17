from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_REPORT_20260412_v0"
)

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_20260412_v0.json"
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
    naming_policy = dict(declaration.get("naming_policy", {}))
    contract = dict(declaration.get("review_contract", {}))

    repeatability_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_review_report", "")
    ).strip()
    named_check_path = REPO_ROOT / str(
        required_inputs.get("bridge_first_named_repeatability_check_report", "")
    ).strip()
    repeatability_review = _read_json(repeatability_review_path)
    named_check = _read_json(named_check_path)
    repeatability_summary = dict(repeatability_review.get("summary", {}))
    named_check_summary = dict(named_check.get("summary", {}))

    repeatability_review_outcome = str(repeatability_summary.get("review_outcome", "")).strip()
    bounded_check_possible_without_full_cycle = bool(
        repeatability_summary.get("bounded_check_possible_without_full_cycle", False)
    )
    observed_comparator_id = str(repeatability_summary.get("external_comparator_id", "")).strip()
    observed_quantity_id = str(repeatability_summary.get("bridge_quantity_id", "")).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
    )

    named_check_declared = (
        str(named_check_summary.get("terminal_outcome", "")).strip()
        == "RL10_BRIDGE_FIRST_NAMED_REPEATABILITY_CHECK_DECLARED"
    )
    if named_check_declared:
        proposed_check_kind = str(named_check_summary.get("proposed_check_kind", "NONE")).strip().upper()
        proposed_check_name = str(named_check_summary.get("proposed_check_name", "")).strip()
        bounded_scope_declared = bool(named_check_summary.get("bounded_scope_declared", False))
        not_disguised_second_full_cycle_declared = bool(
            named_check_summary.get("not_disguised_second_full_cycle_declared", False)
        )
        path_hold_triggered = bool(named_check_summary.get("path_hold_triggered", False))
    else:
        proposed_check_kind = str(naming_policy.get("proposed_check_kind", "NONE")).strip().upper()
        proposed_check_name = str(naming_policy.get("proposed_check_name", "")).strip()
        bounded_scope_declared = bool(naming_policy.get("bounded_scope_declared", False))
        not_disguised_second_full_cycle_declared = bool(
            naming_policy.get("not_disguised_second_full_cycle_declared", False)
        )
        path_hold_triggered = bool(naming_policy.get("path_hold_triggered", False))

    named_check_admissible = (
        bool(proposed_check_name)
        and bounded_scope_declared
        and not_disguised_second_full_cycle_declared
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(contract.get("default_outcome", "NO_SPECIFIC_CHECK_JUSTIFIED_YET")).strip()

    if (
        path_hold_triggered
        or repeatability_review_outcome == "PATH_FALSIFIED"
        or not scope_match
    ):
        review_outcome = "PATH_HOLD_CONTINUES"
        next_action = "HOLD_PATH_AND_REVIEW_SCOPE_OR_PATH_VALIDITY"
    elif (
        repeatability_review_outcome == "LIMITED_HOLD_RETAINED"
        and not bounded_check_possible_without_full_cycle
        and proposed_check_kind == "REPEATABILITY"
        and named_check_admissible
    ):
        review_outcome = "BOUNDED_REPEATABILITY_CHECK_NAMED"
        next_action = "PREPARE_ONE_BOUNDED_REPEATABILITY_CHECK_PACKET"
    elif (
        repeatability_review_outcome == "LIMITED_HOLD_RETAINED"
        and not bounded_check_possible_without_full_cycle
        and proposed_check_kind == "CROSS_PROBE"
        and named_check_admissible
    ):
        review_outcome = "BOUNDED_CROSS_PROBE_CHECK_NAMED"
        next_action = "PREPARE_ONE_BOUNDED_CROSS_PROBE_CHECK_PACKET"
    else:
        review_outcome = "NO_SPECIFIC_CHECK_JUSTIFIED_YET"
        next_action = "RETAIN_LIMITED_HOLD_UNTIL_ONE_ADMISSIBLE_BOUNDED_CHECK_IS_NAMED"

    if review_outcome not in allowed_outcomes:
        review_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "repeatability_review_input_present": bool(repeatability_review_outcome),
            "same_comparator_and_quantity_preserved": scope_match,
            "named_check_admissible": named_check_admissible,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip() == "EXACTLY_ONE_ALLOWED_REPEATABILITY_CHECK_NAMING_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_REPEATABILITY_CHECK_NAMING_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "boundedness_not_full_cycle_explicit": bounded_scope_declared
                and not_disguised_second_full_cycle_declared,
            },
            "inputs": {
                "repeatability_review_outcome": repeatability_review_outcome,
                "bounded_check_possible_without_full_cycle": bounded_check_possible_without_full_cycle,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
                "proposed_check_kind": proposed_check_kind,
                "proposed_check_name": proposed_check_name,
                "named_check_admissible": named_check_admissible,
                "bounded_scope_declared": bounded_scope_declared,
                "not_disguised_second_full_cycle_declared": not_disguised_second_full_cycle_declared,
                "path_hold_triggered": path_hold_triggered,
                "named_check_package_declared": named_check_declared,
            },
            "summary": {
                "all_criteria_satisfied": review_outcome
                in {
                    "BOUNDED_REPEATABILITY_CHECK_NAMED",
                    "BOUNDED_CROSS_PROBE_CHECK_NAMED",
                    "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "proposed_check_kind": proposed_check_kind,
            "proposed_check_name": proposed_check_name,
            "named_check_admissible": named_check_admissible,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_repeatability_review_report": _ptr(repeatability_review_path),
            "bridge_first_named_repeatability_check_report": _ptr(named_check_path),
        },
        "non_claim_boundary": "Repository-local bridge repeatability-check naming review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge repeatability-check naming review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
    )
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
        "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_report: "
        f"review_outcome={payload['summary']['review_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
