from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_REPORT_20260414_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_20260414_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("bounded_check_family_policy", {}))
    contract = dict(declaration.get("bounded_check_family_contract", {}))

    repeatability_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_review_report", "")
    ).strip()
    naming_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_check_naming_review_report", "")
    ).strip()
    comparator_report_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_single_baseline_comparator_report", "")
    ).strip()
    note_path = REPO_ROOT / str(required_inputs.get("bounded_check_family_standard_note", "")).strip()

    repeatability_review = _read_json(repeatability_review_path)
    naming_review = _read_json(naming_review_path)
    comparator_report = _read_json(comparator_report_path)
    note_text = _read_text(note_path)

    repeatability_summary = dict(repeatability_review.get("summary", {}))
    repeatability_inputs = dict(dict(repeatability_review.get("objective_quality", {})).get("inputs", {}))
    naming_summary = dict(naming_review.get("summary", {}))
    naming_inputs = dict(dict(naming_review.get("objective_quality", {})).get("inputs", {}))
    comparator_summary = dict(comparator_report.get("summary", {}))

    repeatability_review_outcome = str(repeatability_summary.get("review_outcome", "")).strip()
    naming_review_outcome = str(naming_summary.get("review_outcome", "")).strip()
    baseline_comparator_id = str(comparator_summary.get("baseline_id", "")).strip()
    repeatability_observed_comparator_id = str(
        repeatability_inputs.get("observed_comparator_id", "")
    ).strip()
    naming_observed_comparator_id = str(naming_inputs.get("observed_comparator_id", "")).strip()
    bridge_quantity_id = str(naming_inputs.get("observed_quantity_id", "")).strip()

    required_repeatability_review_outcome = str(
        policy.get("required_repeatability_review_outcome", "")
    ).strip()
    allowed_naming_review_outcomes = set(policy.get("allowed_naming_review_outcomes", []))
    required_baseline_comparator_id = str(policy.get("required_baseline_comparator_id", "")).strip()
    required_bridge_quantity_id = str(policy.get("required_bridge_quantity_id", "")).strip()
    required_note_tokens = list(policy.get("required_note_tokens", []))
    declaration_standard_id = str(policy.get("declaration_standard_id", "")).strip()
    policy_surface_id = str(policy.get("policy_surface_id", "")).strip()
    first_bounded_check_family_id = str(policy.get("first_bounded_check_family_id", "")).strip()

    note_tokens_present = all(token in note_text for token in required_note_tokens)

    policy_shape_ok = all(
        key in policy
        for key in [
            "required_repeatability_review_outcome",
            "allowed_naming_review_outcomes",
            "required_baseline_comparator_id",
            "required_bridge_quantity_id",
            "required_note_tokens",
            "declaration_standard_id",
            "policy_surface_id",
            "first_bounded_check_family_id",
            "single_layer_only",
            "single_outcome_only",
        ]
    )

    preconditions_ok = (
        repeatability_review_outcome == required_repeatability_review_outcome
        and naming_review_outcome in allowed_naming_review_outcomes
        and baseline_comparator_id == required_baseline_comparator_id
        and repeatability_observed_comparator_id == required_baseline_comparator_id
        and naming_observed_comparator_id == required_baseline_comparator_id
        and bridge_quantity_id == required_bridge_quantity_id
        and note_tokens_present
        and bool(declaration_standard_id)
        and bool(policy_surface_id)
        and bool(first_bounded_check_family_id)
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(
        contract.get(
            "default_outcome",
            "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_EVIDENCE_INCOMPLETE",
        )
    ).strip()

    if not policy_shape_ok:
        terminal_outcome = "HOLD_PENDING_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_REPAIR"
        next_action = "REPAIR_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_SHAPE"
    elif preconditions_ok:
        terminal_outcome = "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED"
        next_action = "NAME_ONE_ADMISSIBLE_BOUNDED_CHECK_AND_DEFINE_MINIMUM_SECOND_CYCLE_EVIDENCE"
    else:
        terminal_outcome = "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_PRECONDITIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    declaration_standard_defined = terminal_outcome == "RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_DECLARED"
    bounded_check_families_defined = declaration_standard_defined
    external_validation_policy_surface_defined = declaration_standard_defined

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "repeatability_review_outcome_match": repeatability_review_outcome
            == required_repeatability_review_outcome,
            "naming_review_outcome_allowed": naming_review_outcome in allowed_naming_review_outcomes,
            "baseline_comparator_id_match": baseline_comparator_id == required_baseline_comparator_id,
            "repeatability_observed_comparator_id_match": repeatability_observed_comparator_id
            == required_baseline_comparator_id,
            "naming_observed_comparator_id_match": naming_observed_comparator_id
            == required_baseline_comparator_id,
            "bridge_quantity_id_match": bridge_quantity_id == required_bridge_quantity_id,
            "note_tokens_present": note_tokens_present,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_RL10_BRIDGE_BOUNDED_CHECK_FAMILY_STANDARD_LAYER_ONLY",
            "declaration_standard_defined": declaration_standard_defined,
            "bounded_check_families_defined": bounded_check_families_defined,
            "external_validation_policy_surface_defined": external_validation_policy_surface_defined,
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "bounded_check_family_standard_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "repeatability_review_outcome": repeatability_review_outcome,
                "required_repeatability_review_outcome": required_repeatability_review_outcome,
                "naming_review_outcome": naming_review_outcome,
                "allowed_naming_review_outcomes": sorted(allowed_naming_review_outcomes),
                "baseline_comparator_id": baseline_comparator_id,
                "required_baseline_comparator_id": required_baseline_comparator_id,
                "repeatability_observed_comparator_id": repeatability_observed_comparator_id,
                "naming_observed_comparator_id": naming_observed_comparator_id,
                "bridge_quantity_id": bridge_quantity_id,
                "required_bridge_quantity_id": required_bridge_quantity_id,
                "declaration_standard_defined": declaration_standard_defined,
                "bounded_check_families_defined": bounded_check_families_defined,
                "external_validation_policy_surface_defined": external_validation_policy_surface_defined,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "declaration_standard_defined": declaration_standard_defined,
            "bounded_check_families_defined": bounded_check_families_defined,
            "external_validation_policy_surface_defined": external_validation_policy_surface_defined,
            "first_bounded_check_family_id": first_bounded_check_family_id,
            "next_action": next_action,
            "single_layer_only": bool(policy.get("single_layer_only", True)),
            "single_outcome_only": bool(policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_repeatability_review_report": _ptr(repeatability_review_path),
            "bridge_repeatability_check_naming_review_report": _ptr(naming_review_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_report_path),
            "bounded_check_family_standard_note": _ptr(note_path),
        },
        "non_claim_boundary": "Repository-local RL10 bridge bounded check family standard report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate RL10 bridge bounded check family standard report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_20260414_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_bounded_check_family_standard_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())