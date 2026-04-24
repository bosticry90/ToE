from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_CHARACTERIZATION_PACKET_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_CHARACTERIZATION_PACKET_20260422_v0.json"
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
    limitation_class_policy = dict(declaration.get("limitation_class_policy", {}))
    contract = dict(declaration.get("packet_contract", {}))

    limitation_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_limitation_review_report", "")
    ).strip()
    significance_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_significance_adjudication_report", "")
    ).strip()

    limitation_review = _read_json(limitation_review_path)
    significance = _read_json(significance_path)

    lr_summary = dict(limitation_review.get("summary", {}))
    sig_summary = dict(significance.get("summary", {}))
    sig_inputs = dict(dict(significance.get("objective_quality", {})).get("inputs", {}))

    review_outcome = str(lr_summary.get("review_outcome", "")).strip()
    limitation_primary_cause = str(lr_summary.get("limitation_primary_cause", "")).strip()
    local_and_refinable = bool(lr_summary.get("local_and_refinable", False))
    signal_margin = float(lr_summary.get("signal_margin", 0.0))
    significance_outcome = str(sig_summary.get("adjudication_outcome", "")).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    observed_comparator_id = str(lr_summary.get("external_comparator_id", "")).strip()
    observed_quantity_id = str(lr_summary.get("bridge_quantity_id", "")).strip()
    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
    )

    success_margin_min = float(
        limitation_class_policy.get("external_path_success_signal_margin_min", 0.05)
    )
    signal_margin_gap = round(success_margin_min - signal_margin, 6)
    comparator_repeatability_confirmed = bool(
        sig_inputs.get("comparator_repeatability_confirmed", False)
    )
    cross_probe_consistency_confirmed = bool(
        sig_inputs.get("cross_probe_consistency_confirmed", False)
    )

    # Determine dominant limitation class from limitation review outcome
    if not scope_match:
        dominant_limitation_class = "LIMITATION_CLASS_INDETERMINATE"
        packet_outcome = "LIMITATION_CLASS_INDETERMINATE"
        dominant_factor_summary = "scope_mismatch_prevents_class_determination"
    elif review_outcome == "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD" and (
        not comparator_repeatability_confirmed or not cross_probe_consistency_confirmed
    ):
        dominant_limitation_class = "comparator_bound_limitation"
        packet_outcome = "COMPARATOR_BOUND_LIMITATION_CONFIRMED"
        dominant_factor_summary = (
            "comparator_repeatability_not_yet_confirmed_signal_margin_below_external_path_threshold"
        )
    elif review_outcome == "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD":
        dominant_limitation_class = "robustness_margin_limitation"
        packet_outcome = "ROBUSTNESS_MARGIN_LIMITATION_CONFIRMED"
        dominant_factor_summary = "signal_margin_below_external_path_success_threshold"
    elif review_outcome == "LIMITATION_LOCAL_REFINABLE_ONE_MORE_BOUNDED_COMPARATOR_CYCLE_JUSTIFIED":
        dominant_limitation_class = "signal_stability_limitation"
        packet_outcome = "SIGNAL_STABILITY_LIMITATION_CONFIRMED"
        dominant_factor_summary = "local_signal_discrimination_insufficient_one_more_cycle_may_resolve"
    elif review_outcome == "LIMITATION_INTERPRETATION_SCOPE_HOLD":
        dominant_limitation_class = "probe_sensitivity_limitation"
        packet_outcome = "PROBE_SENSITIVITY_LIMITATION_CONFIRMED"
        dominant_factor_summary = "interpretation_scope_or_path_validity_insufficient"
    else:
        dominant_limitation_class = "LIMITATION_CLASS_INDETERMINATE"
        packet_outcome = "LIMITATION_CLASS_INDETERMINATE"
        dominant_factor_summary = "limitation_review_outcome_does_not_map_to_admitted_class"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if packet_outcome not in allowed_outcomes:
        packet_outcome = str(contract.get("default_outcome", "COMPARATOR_BOUND_LIMITATION_CONFIRMED")).strip()

    all_criteria_satisfied = (
        scope_match
        and bool(limitation_primary_cause)
        and bool(significance_outcome == "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED")
        and packet_outcome in allowed_outcomes
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "significance_outcome_is_probe_signal_confirmed_but_limited": significance_outcome
            == "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
            "limitation_review_outcome_present": bool(review_outcome),
            "scope_match_confirmed": scope_match,
            "single_dominant_class_resolved": dominant_limitation_class
            != "LIMITATION_CLASS_INDETERMINATE",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_LIMITATION_CHARACTERIZATION_PACKET_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_LIMITATION_CHARACTERIZATION_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": packet_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "dominant_limitation_class_named": dominant_limitation_class
                != "LIMITATION_CLASS_INDETERMINATE",
                "all_criteria_satisfied": all_criteria_satisfied,
            },
            "inputs": {
                "significance_outcome": significance_outcome,
                "limitation_review_outcome": review_outcome,
                "limitation_primary_cause": limitation_primary_cause,
                "local_and_refinable": local_and_refinable,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": success_margin_min,
                "signal_margin_gap_below_threshold": signal_margin_gap,
                "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
            },
            "summary": {
                "all_criteria_satisfied": all_criteria_satisfied,
                "phase_status": "COMPLETE",
                "next_action": "KEEP_BRIDGE_SEAM_PRIMARY_WITH_BOUNDED_LIMITATION_DISCIPLINE",
            },
        },
        "summary": {
            "single_question": "What is the dominant limiting factor behind PROBE_SIGNAL_CONFIRMED_BUT_LIMITED?",
            "packet_outcome": packet_outcome,
            "dominant_limitation_class": dominant_limitation_class,
            "dominant_factor_summary": dominant_factor_summary,
            "signal_margin": signal_margin,
            "signal_margin_gap_below_threshold": signal_margin_gap,
            "external_path_success_signal_margin_min": success_margin_min,
            "local_and_refinable": local_and_refinable,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": "KEEP_BRIDGE_SEAM_PRIMARY_WITH_BOUNDED_LIMITATION_DISCIPLINE",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_limitation_review_report": _ptr(limitation_review_path),
            "bridge_probe_significance_adjudication_report": _ptr(significance_path),
        },
        "non_claim_boundary": "Repository-local bridge limitation-characterization packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge limitation-characterization packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_characterization_packet_20260422_v0.json",
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
    print(f"qm_stat_rl10_discrete_transition_bridge_limitation_characterization_packet_report: {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
