from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_REVIEW_REPORT_20260412_v0"
_FP_TOLERANCE = 1e-9

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_REVIEW_20260412_v0.json"
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
    diagnosis_policy = dict(declaration.get("diagnosis_policy", {}))
    contract = dict(declaration.get("review_contract", {}))

    significance_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_significance_adjudication_report", "")
    ).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("bridge_probe_execution_report", "")).strip()
    ruling_path = REPO_ROOT / str(required_inputs.get("bridge_probe_ruling_report", "")).strip()

    significance = _read_json(significance_path)
    execution = _read_json(execution_path)
    ruling = _read_json(ruling_path)

    significance_summary = dict(significance.get("summary", {}))
    significance_inputs = dict(dict(significance.get("objective_quality", {})).get("inputs", {}))
    execution_summary = dict(execution.get("summary", {}))
    ruling_summary = dict(ruling.get("summary", {}))

    significance_outcome = str(significance_summary.get("adjudication_outcome", "")).strip()
    execution_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    ruling_outcome = str(ruling_summary.get("terminal_outcome", "")).strip()
    ruling_status = str(ruling_summary.get("ruling_status", "")).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    observed_comparator_id = str(execution_summary.get("external_comparator_id", "")).strip()
    observed_quantity_id = str(execution_summary.get("bridge_quantity_id", "")).strip()
    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
    )

    signal_margin = float(execution_summary.get("signal_margin", 0.0))
    success_margin_min = float(
        diagnosis_policy.get(
            "external_path_success_signal_margin_min",
            significance_inputs.get("external_path_success_signal_margin_min", 0.05),
        )
    )
    comparator_repeatability_confirmed = bool(
        significance_inputs.get("comparator_repeatability_confirmed", False)
    )
    cross_probe_consistency_confirmed = bool(
        significance_inputs.get("cross_probe_consistency_confirmed", False)
    )
    auto_authorize_additional_cycle = bool(diagnosis_policy.get("auto_authorize_additional_cycle", False))

    if (
        significance_outcome == "PROBE_SIGNAL_REQUIRES_ONE_MORE_BOUNDED_COMPARATOR_CYCLE"
        and execution_outcome in {"PROBE_SIGNAL_NONDISCRIMINATIVE", "PROBE_SIGNAL_INCONCLUSIVE"}
        and ruling_outcome in {"PROBE_SIGNAL_NONDISCRIMINATIVE", "PROBE_SIGNAL_INCONCLUSIVE"}
    ):
        review_outcome = "LIMITATION_LOCAL_REFINABLE_ONE_MORE_BOUNDED_COMPARATOR_CYCLE_JUSTIFIED"
        limitation_primary_cause = "local_signal_discrimination_insufficient"
        one_more_cycle_justified = True
        local_and_refinable = True
        next_action = "AUTHORIZE_ONE_ADDITIONAL_BOUNDED_COMPARATOR_CYCLE"
    elif (
        significance_outcome == "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED"
        and ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and execution_outcome == "PROBE_SIGNAL_CONFIRMED"
        and ruling_outcome == "PROBE_SIGNAL_CONFIRMED"
        and (not comparator_repeatability_confirmed or not cross_probe_consistency_confirmed)
    ):
        review_outcome = "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD"
        limitation_primary_cause = "comparator_repeatability_or_cross_probe_consistency_not_yet_confirmed"
        one_more_cycle_justified = False if not auto_authorize_additional_cycle else True
        local_and_refinable = True
        next_action = "KEEP_SEAM_ACTIVE_AS_LIMITED_AND_PREPARE_BOUNDED_LIMITATION_HARDENING"
    elif (
        significance_outcome == "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED"
        and ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and execution_outcome == "PROBE_SIGNAL_CONFIRMED"
        and ruling_outcome == "PROBE_SIGNAL_CONFIRMED"
        and signal_margin < success_margin_min - _FP_TOLERANCE
    ):
        review_outcome = "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD"
        limitation_primary_cause = "signal_margin_below_external_path_success_threshold"
        one_more_cycle_justified = False if not auto_authorize_additional_cycle else True
        local_and_refinable = True
        next_action = "KEEP_SEAM_ACTIVE_AND_TIGHTEN_SIGNAL_MARGIN_IN_BOUNDED_MODE"
    else:
        review_outcome = "LIMITATION_INTERPRETATION_SCOPE_HOLD"
        limitation_primary_cause = "interpretation_scope_or_path_validity_not_sufficient_for_advancement"
        one_more_cycle_justified = False
        local_and_refinable = False
        next_action = "HOLD_SCOPE_AND_REVIEW_INTERPRETATION_BOUNDARIES"

    if not scope_match:
        review_outcome = "LIMITATION_INTERPRETATION_SCOPE_HOLD"
        limitation_primary_cause = "scope_mismatch_between_declared_and_observed_comparator_or_quantity"
        one_more_cycle_justified = False
        local_and_refinable = False
        next_action = "HOLD_SCOPE_AND_RESTORE_DECLARED_SEAM_BINDING"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if review_outcome not in allowed_outcomes:
        review_outcome = str(contract.get("default_outcome", "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD")).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "significance_input_present": bool(significance_outcome),
            "same_comparator_and_quantity_preserved": scope_match,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_LIMITATION_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_LIMITATION_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "limitation_diagnosis_answered": bool(limitation_primary_cause),
            },
            "inputs": {
                "significance_outcome": significance_outcome,
                "execution_outcome": execution_outcome,
                "ruling_status": ruling_status,
                "ruling_outcome": ruling_outcome,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": success_margin_min,
                "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                "auto_authorize_additional_cycle": auto_authorize_additional_cycle,
            },
            "summary": {
                "all_criteria_satisfied": review_outcome
                in {
                    "LIMITATION_LOCAL_REFINABLE_ONE_MORE_BOUNDED_COMPARATOR_CYCLE_JUSTIFIED",
                    "LIMITATION_COMPARATOR_BOUND_CONFIRMED_SIGNAL_HOLD",
                    "LIMITATION_SIGNAL_MARGIN_CONFIRMED_SIGNAL_HOLD",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "limitation_primary_cause": limitation_primary_cause,
            "local_and_refinable": local_and_refinable,
            "one_more_bounded_comparator_cycle_justified": one_more_cycle_justified,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin": signal_margin,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_probe_significance_adjudication_report": _ptr(significance_path),
            "bridge_probe_execution_report": _ptr(execution_path),
            "bridge_probe_ruling_report": _ptr(ruling_path),
        },
        "non_claim_boundary": "Repository-local bridge limitation review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge limitation review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_review_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_limitation_review_report: "
        f"review_outcome={payload['summary']['review_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
