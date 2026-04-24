from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# Absolute tolerance for floating-point boundary comparisons (margin >= stability_floor).
_FP_TOLERANCE = 1e-9

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_20260422_v0.json"
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


def _sample_margins(nominal_margin: float, perturbations: list[float]) -> list[float]:
    """Return signal margins at each adverse perturbation point.

    A positive perturbation value reduces the signal margin (adverse direction).
    """
    return [nominal_margin - delta for delta in perturbations]


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)

    required_inputs = dict(declaration.get("required_inputs", {}))
    seam_scope = dict(declaration.get("seam_scope", {}))
    window_params = dict(declaration.get("window_parameters", {}))
    check_policy = dict(declaration.get("check_policy", {}))
    contract = dict(declaration.get("check_contract", {}))

    probe_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_execution_report", "")
    ).strip()
    naming_review_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_check_naming_review_report", "")
    ).strip()
    admissibility_path = REPO_ROOT / str(
        required_inputs.get("bridge_material_repeatability_admissibility_criteria_report", "")
    ).strip()

    probe_report = _read_json(probe_path)
    naming_review = _read_json(naming_review_path)
    admissibility = _read_json(admissibility_path)

    # Extract probe signal data
    probe_summary = dict(probe_report.get("summary", {}))
    probe_inputs = dict(probe_report.get("objective_quality", {}).get("inputs", {}))
    nominal_signal_margin = float(
        probe_inputs.get("signal_margin", probe_summary.get("signal_margin", 0.0))
    )
    probe_signal_strength = float(probe_inputs.get("probe_signal_strength", 0.0))
    probe_signal_threshold = float(probe_inputs.get("probe_signal_threshold", 0.0))
    probe_terminal_outcome = str(probe_summary.get("terminal_outcome", "")).strip()
    probe_comparator_id = str(probe_summary.get("external_comparator_id", "")).strip()
    probe_quantity_id = str(probe_summary.get("bridge_quantity_id", "")).strip()

    # Extract naming review data
    naming_summary = dict(naming_review.get("summary", {}))
    naming_review_outcome = str(naming_summary.get("review_outcome", "")).strip()
    named_check_id_from_review = str(naming_summary.get("proposed_check_name", "")).strip()
    named_check_kind = str(naming_summary.get("proposed_check_kind", "")).strip()

    # Extract admissibility data
    admissibility_summary = dict(admissibility.get("summary", {}))
    admissibility_outcome = str(admissibility_summary.get("terminal_outcome", "")).strip()

    # Window parameters
    window_half_width = float(window_params.get("window_half_width", 0.02))
    stability_floor = float(window_params.get("stability_floor", 0.02))
    sample_perturbations = [
        float(v) for v in window_params.get("sample_perturbations", [0.0, window_half_width])
    ]

    # Expected values from seam scope
    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    expected_check_id = str(seam_scope.get("named_check_id", "")).strip()
    expected_check_family_id = str(seam_scope.get("check_family_id", "")).strip()

    # Policy requirements
    required_naming_outcome = str(check_policy.get("required_naming_review_outcome", "")).strip()
    required_naming_check_id = str(check_policy.get("required_naming_check_id", "")).strip()
    required_admissibility_outcome = str(
        check_policy.get("required_admissibility_criteria_outcome", "")
    ).strip()
    not_a_full_second_cycle = bool(check_policy.get("not_a_full_second_cycle", True))
    no_scope_expansion = bool(check_policy.get("no_scope_expansion", True))

    # Precondition checks
    comparator_id_matches = probe_comparator_id == expected_comparator_id
    quantity_id_matches = probe_quantity_id == expected_quantity_id
    naming_outcome_matches = naming_review_outcome == required_naming_outcome
    check_id_matches = named_check_id_from_review == required_naming_check_id
    check_id_matches_scope = named_check_id_from_review == expected_check_id
    admissibility_matches = admissibility_outcome == required_admissibility_outcome
    scope_guards_satisfied = not_a_full_second_cycle and no_scope_expansion
    probe_signal_confirmed = probe_terminal_outcome == "PROBE_SIGNAL_CONFIRMED"

    preconditions_satisfied = (
        comparator_id_matches
        and quantity_id_matches
        and naming_outcome_matches
        and check_id_matches
        and check_id_matches_scope
        and admissibility_matches
        and scope_guards_satisfied
        and probe_signal_confirmed
    )

    scope_is_admissible = (
        comparator_id_matches
        and quantity_id_matches
        and check_id_matches_scope
        and scope_guards_satisfied
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    # Execute window check
    if not preconditions_satisfied and not scope_is_admissible:
        window_check_outcome = "WINDOW_CHECK_PRECONDITION_FAILED"
        window_check_comparator_stable = False
        window_check_ruling = "PRECONDITIONS_NOT_MET"
        sampled_margins: list[float] = []
        min_margin_within_window: float | None = None
        window_check_executed = False
        next_action = "REPAIR_WINDOW_CHECK_PRECONDITIONS_BEFORE_EXECUTION"
    elif not preconditions_satisfied and scope_is_admissible:
        window_check_outcome = "WINDOW_CHECK_SCOPE_VIOLATION"
        window_check_comparator_stable = False
        window_check_ruling = "SCOPE_ADMISSIBLE_BUT_NAMING_OR_ADMISSIBILITY_PRECONDITION_FAILED"
        sampled_margins = []
        min_margin_within_window = None
        window_check_executed = False
        next_action = "REPAIR_NAMING_AND_ADMISSIBILITY_PRECONDITIONS"
    else:
        # Execute the window check
        sampled_margins = _sample_margins(nominal_signal_margin, sample_perturbations)
        min_margin_within_window = min(sampled_margins)
        window_check_executed = True

        if min_margin_within_window >= stability_floor - _FP_TOLERANCE:
            window_check_comparator_stable = True
            window_check_outcome = "WINDOW_CHECK_COMPARATOR_STABLE"
            window_check_ruling = (
                f"MIN_MARGIN_{min_margin_within_window:.4f}_AT_OR_ABOVE_STABILITY_FLOOR_{stability_floor:.4f}"
            )
            next_action = (
                "UPDATE_COMPARATOR_REPEATABILITY_CONFIRMATION_DECLARATION_AND_RERUN_CONFIRMATION_REPORT"
            )
        else:
            window_check_comparator_stable = False
            window_check_outcome = "WINDOW_CHECK_COMPARATOR_NOT_STABLE"
            window_check_ruling = (
                f"MIN_MARGIN_{min_margin_within_window:.4f}_BELOW_STABILITY_FLOOR_{stability_floor:.4f}"
            )
            next_action = "RETAIN_HOLD_SIGNAL_MARGIN_BELOW_STABILITY_FLOOR_WITHIN_WINDOW"

    if window_check_outcome not in allowed_outcomes:
        window_check_outcome = str(
            contract.get("default_outcome", "WINDOW_CHECK_COMPARATOR_NOT_STABLE")
        ).strip()

    all_criteria_satisfied = preconditions_satisfied and (window_check_outcome in allowed_outcomes)

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "comparator_id_matches_scope": comparator_id_matches,
            "quantity_id_matches_scope": quantity_id_matches,
            "naming_review_outcome_is_bounded_check_named": naming_outcome_matches,
            "named_check_id_matches_required": check_id_matches,
            "named_check_id_matches_seam_scope": check_id_matches_scope,
            "admissibility_criteria_declared": admissibility_matches,
            "probe_signal_confirmed": probe_signal_confirmed,
            "scope_guards_satisfied": scope_guards_satisfied,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_SIGMA_DB_REPEATABILITY_WINDOW_CHECK_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_WINDOW_CHECK_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied,
                "window_check_executed": window_check_executed,
                "allowed_outcome_materialized": window_check_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "all_criteria_satisfied": all_criteria_satisfied,
            },
            "inputs": {
                "nominal_signal_margin": nominal_signal_margin,
                "probe_signal_strength": probe_signal_strength,
                "probe_signal_threshold": probe_signal_threshold,
                "probe_terminal_outcome": probe_terminal_outcome,
                "probe_comparator_id": probe_comparator_id,
                "probe_quantity_id": probe_quantity_id,
                "naming_review_outcome": naming_review_outcome,
                "named_check_id_from_review": named_check_id_from_review,
                "named_check_kind": named_check_kind,
                "admissibility_outcome": admissibility_outcome,
                "window_half_width": window_half_width,
                "stability_floor": stability_floor,
                "sample_perturbations": sample_perturbations,
                "expected_comparator_id": expected_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "expected_check_id": expected_check_id,
                "expected_check_family_id": expected_check_family_id,
            },
            "window_execution": {
                "sampled_margins": sampled_margins,
                "min_margin_within_window": min_margin_within_window,
                "window_check_passes": window_check_comparator_stable,
            },
            "summary": {
                "all_criteria_satisfied": all_criteria_satisfied,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "window_check_outcome": window_check_outcome,
            "window_check_ruling": window_check_ruling,
            "window_check_comparator_stable": window_check_comparator_stable,
            "check_id": expected_check_id,
            "check_family_id": expected_check_family_id,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "nominal_signal_margin": nominal_signal_margin,
            "window_half_width": window_half_width,
            "stability_floor": stability_floor,
            "min_margin_within_window": min_margin_within_window,
            "no_promotion_claim": True,
            "no_seam_closure": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_probe_execution_report": _ptr(probe_path),
            "bridge_repeatability_check_naming_review_report": _ptr(naming_review_path),
            "bridge_material_repeatability_admissibility_criteria_report": _ptr(admissibility_path),
        },
        "non_claim_boundary": "Repository-local bounded repeatability window check report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge sigma_db repeatability window check report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_sigma_db_repeatability_window_check_20260422_v0.json",
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
        f"qm_stat_rl10_discrete_transition_bridge_sigma_db_repeatability_window_check_report: {out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
