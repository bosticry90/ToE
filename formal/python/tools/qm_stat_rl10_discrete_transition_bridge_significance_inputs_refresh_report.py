from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNIFICANCE_INPUTS_REFRESH_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNIFICANCE_INPUTS_REFRESH_20260422_v0.json"
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

    significance_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_significance_adjudication_report", "")
    ).strip()
    confirmation_path = REPO_ROOT / str(
        required_inputs.get("bridge_comparator_repeatability_confirmation_report", "")
    ).strip()

    significance = _read_json(significance_path)
    confirmation = _read_json(confirmation_path)

    sig_summary = dict(significance.get("summary", {}))
    sig_inputs = dict(
        dict(significance.get("objective_quality", {})).get("inputs", {})
    )
    conf_summary = dict(confirmation.get("summary", {}))

    # Read existing significance inputs
    adjudication_outcome = str(sig_summary.get("adjudication_outcome", "")).strip()
    prior_comparator_repeatability = bool(
        sig_inputs.get("comparator_repeatability_confirmed", False)
    )
    cross_probe_consistency_confirmed = bool(
        sig_inputs.get("cross_probe_consistency_confirmed",
                       bool(refresh_policy.get("cross_probe_consistency_confirmed", False)))
    )
    signal_margin = float(sig_inputs.get("signal_margin", 0.0))
    external_path_success_signal_margin_min = float(
        sig_inputs.get("external_path_success_signal_margin_min", 0.05)
    )
    confirmed_but_limited_signal_margin_min = float(
        sig_inputs.get("confirmed_but_limited_signal_margin_min", 0.02)
    )
    one_more_cycle_signal_margin_min = float(
        sig_inputs.get("one_more_cycle_signal_margin_min", 0.0)
    )

    # Read confirmation result
    confirmation_outcome = str(conf_summary.get("confirmation_outcome", "")).strip()
    conf_named_check_id = str(conf_summary.get("named_check_id", "")).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    sig_comparator_id = str(sig_summary.get("external_comparator_id", "")).strip()
    sig_quantity_id = str(sig_summary.get("bridge_quantity_id", "")).strip()

    required_significance_outcome = str(
        refresh_policy.get("required_significance_outcome", "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED")
    ).strip()
    required_repeatability_confirmation_outcome = str(
        refresh_policy.get(
            "required_repeatability_confirmation_outcome", "COMPARATOR_REPEATABILITY_CONFIRMED"
        )
    ).strip()

    # Scope check
    scope_match = (
        sig_comparator_id == expected_comparator_id and sig_quantity_id == expected_quantity_id
    )

    # Precondition check
    significance_outcome_matches = adjudication_outcome == required_significance_outcome
    repeatability_confirmation_matches = confirmation_outcome == required_repeatability_confirmation_outcome
    scope_guards_satisfied = bool(refresh_policy.get("not_a_new_adjudication_cycle", True)) and bool(
        refresh_policy.get("no_scope_expansion", True)
    )

    preconditions_satisfied = (
        significance_outcome_matches
        and repeatability_confirmation_matches
        and scope_match
        and scope_guards_satisfied
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not preconditions_satisfied:
        refresh_outcome = "SIGNIFICANCE_INPUTS_REFRESH_PRECONDITION_FAILED"
        updated_comparator_repeatability_confirmed = prior_comparator_repeatability
        next_action = "REPAIR_SIGNIFICANCE_INPUTS_REFRESH_PRECONDITIONS"
        inputs_changed = False
    elif confirmation_outcome == required_repeatability_confirmation_outcome and not prior_comparator_repeatability:
        refresh_outcome = "SIGNIFICANCE_INPUTS_REFRESHED"
        updated_comparator_repeatability_confirmed = True
        inputs_changed = True
        next_action = "RERUN_LIMITATION_REVIEW_WITH_REFRESHED_SIGNIFICANCE_INPUTS"
    else:
        # Confirmation outcome matches but nothing changed (already confirmed, or outcome not confirmatory)
        refresh_outcome = "SIGNIFICANCE_INPUTS_UNCHANGED"
        updated_comparator_repeatability_confirmed = prior_comparator_repeatability
        inputs_changed = False
        next_action = "RERUN_LIMITATION_REVIEW_WITH_REFRESHED_SIGNIFICANCE_INPUTS"

    if refresh_outcome not in allowed_outcomes:
        refresh_outcome = str(
            contract.get("default_outcome", "SIGNIFICANCE_INPUTS_UNCHANGED")
        ).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "significance_outcome_matches_required": significance_outcome_matches,
            "repeatability_confirmation_matches_required": repeatability_confirmation_matches,
            "comparator_and_quantity_scope_match": scope_match,
            "scope_guards_satisfied": scope_guards_satisfied,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_SIGNIFICANCE_INPUTS_REFRESH_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SIGNIFICANCE_INPUTS_REFRESH_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied,
                "allowed_outcome_materialized": refresh_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "all_criteria_satisfied": preconditions_satisfied and (refresh_outcome in allowed_outcomes),
            },
            # This section mirrors the significance adjudication structure so the limitation review
            # tool can consume it directly in place of the original significance adjudication report.
            "inputs": {
                "comparator_repeatability_confirmed": updated_comparator_repeatability_confirmed,
                "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": external_path_success_signal_margin_min,
                "confirmed_but_limited_signal_margin_min": confirmed_but_limited_signal_margin_min,
                "one_more_cycle_signal_margin_min": one_more_cycle_signal_margin_min,
                "prior_comparator_repeatability_confirmed": prior_comparator_repeatability,
                "repeatability_confirmation_outcome": confirmation_outcome,
                "repeatability_named_check_id": conf_named_check_id,
                "expected_comparator_id": expected_comparator_id,
                "expected_quantity_id": expected_quantity_id,
            },
            "summary": {
                "all_criteria_satisfied": preconditions_satisfied and (refresh_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        # summary mirrors significance adjudication shape so limitation review can consume it
        "summary": {
            "adjudication_outcome": adjudication_outcome,
            "refresh_outcome": refresh_outcome,
            "inputs_changed": inputs_changed,
            "comparator_repeatability_confirmed_updated_to": updated_comparator_repeatability_confirmed,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin": signal_margin,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_probe_significance_adjudication_report": _ptr(significance_path),
            "bridge_comparator_repeatability_confirmation_report": _ptr(confirmation_path),
        },
        "non_claim_boundary": "Repository-local bounded significance inputs refresh report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge significance inputs refresh report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_significance_inputs_refresh_20260422_v0.json",
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
        f"qm_stat_rl10_discrete_transition_bridge_significance_inputs_refresh_report: {out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
