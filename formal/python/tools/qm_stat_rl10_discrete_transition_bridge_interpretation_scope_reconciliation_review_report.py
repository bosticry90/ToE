from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_20260422_v0.json"
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
    policy = dict(declaration.get("reconciliation_policy", {}))
    contract = dict(declaration.get("reconciliation_contract", {}))

    significance_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_significance_adjudication_report", "")
    ).strip()
    limitation_path = REPO_ROOT / str(required_inputs.get("bridge_limitation_review_report", "")).strip()
    acceptance_path = REPO_ROOT / str(
        required_inputs.get("bridge_signal_margin_limitation_acceptance_review_report", "")
    ).strip()

    significance = _read_json(significance_path)
    limitation = _read_json(limitation_path)
    acceptance = _read_json(acceptance_path)

    significance_summary = dict(significance.get("summary", {}))
    significance_inputs = dict(dict(significance.get("objective_quality", {})).get("inputs", {}))
    limitation_summary = dict(limitation.get("summary", {}))
    limitation_inputs = dict(dict(limitation.get("objective_quality", {})).get("inputs", {}))
    acceptance_summary = dict(acceptance.get("summary", {}))

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()

    sig_outcome = str(significance_summary.get("adjudication_outcome", "")).strip()
    lim_outcome = str(limitation_summary.get("review_outcome", "")).strip()
    acc_outcome = str(acceptance_summary.get("review_outcome", "")).strip()

    required_sig_outcome = str(
        policy.get(
            "required_significance_outcome_for_external_success_candidate",
            "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE",
        )
    ).strip()
    required_lim_outcome = str(
        policy.get("required_limitation_outcome_for_scope_hold", "LIMITATION_INTERPRETATION_SCOPE_HOLD")
    ).strip()
    required_acc_outcome = str(
        policy.get(
            "required_acceptance_outcome_for_precondition_failure",
            "SIGNAL_MARGIN_LIMITATION_ACCEPTANCE_PRECONDITION_FAILED",
        )
    ).strip()

    sig_matches = sig_outcome == required_sig_outcome
    lim_matches = lim_outcome == required_lim_outcome
    acc_matches = acc_outcome == required_acc_outcome

    sig_comparator_id = str(significance_summary.get("external_comparator_id", "")).strip()
    sig_quantity_id = str(significance_summary.get("bridge_quantity_id", "")).strip()
    lim_comparator_id = str(limitation_summary.get("external_comparator_id", "")).strip()
    lim_quantity_id = str(limitation_summary.get("bridge_quantity_id", "")).strip()
    acc_comparator_id = str(acceptance_summary.get("external_comparator_id", "")).strip()
    acc_quantity_id = str(acceptance_summary.get("bridge_quantity_id", "")).strip()

    scope_match = (
        sig_comparator_id == expected_comparator_id
        and sig_quantity_id == expected_quantity_id
        and lim_comparator_id == expected_comparator_id
        and lim_quantity_id == expected_quantity_id
        and acc_comparator_id == expected_comparator_id
        and acc_quantity_id == expected_quantity_id
    )

    scope_guards_satisfied = bool(policy.get("not_a_new_hardening_cycle", True)) and bool(
        policy.get("no_scope_expansion", True)
    )

    preconditions_satisfied = sig_matches and lim_matches and acc_matches and scope_guards_satisfied

    declaration_mapping_mismatch_if_external_success_and_scope_hold = bool(
        policy.get("declaration_mapping_mismatch_if_external_success_and_scope_hold", True)
    )

    signal_margin = float(significance_summary.get("signal_margin", significance_inputs.get("signal_margin", 0.0)))
    success_margin_min = float(
        significance_inputs.get("external_path_success_signal_margin_min", 0.05)
    )
    comparator_repeatability_confirmed = bool(
        significance_inputs.get("comparator_repeatability_confirmed", False)
    )
    cross_probe_consistency_confirmed = bool(
        significance_inputs.get("cross_probe_consistency_confirmed", False)
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        review_outcome = "INTERPRETATION_SCOPE_RECONCILIATION_SCOPE_VIOLATION"
        reconciliation_status = "SCOPE_VIOLATION"
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif not preconditions_satisfied:
        review_outcome = "INTERPRETATION_SCOPE_RECONCILIATION_PRECONDITION_FAILED"
        reconciliation_status = "PRECONDITIONS_NOT_MET"
        next_action = "REPAIR_RECONCILIATION_PRECONDITIONS"
    elif declaration_mapping_mismatch_if_external_success_and_scope_hold:
        review_outcome = "INTERPRETATION_SCOPE_DECLARATION_INPUT_MISMATCH_CONFIRMED"
        reconciliation_status = "MAPPING_MISMATCH_CONFIRMED"
        next_action = "NORMALIZE_LIMITATION_REVIEW_DECLARATION_AND_OUTCOME_MAPPING_BEFORE_ACCEPTANCE_OR_HARDENING"
    else:
        review_outcome = "INTERPRETATION_SCOPE_SHIFT_CONFIRMED_AS_CORRECT"
        reconciliation_status = "SHIFT_CONFIRMED"
        next_action = "RECORD_INTERPRETATION_SCOPE_SHIFT_AS_ACTIVE_BOUNDARY"

    if review_outcome not in allowed_outcomes:
        review_outcome = str(
            contract.get("default_outcome", "INTERPRETATION_SCOPE_RECONCILIATION_PRECONDITION_FAILED")
        ).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "significance_outcome_matches_required": sig_matches,
            "limitation_outcome_matches_required": lim_matches,
            "acceptance_outcome_matches_required": acc_matches,
            "scope_guards_satisfied": scope_guards_satisfied,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_INTERPRETATION_SCOPE_RECONCILIATION_REVIEW_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_INTERPRETATION_SCOPE_RECONCILIATION_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied and scope_match,
                "allowed_outcome_materialized": review_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "reconciliation_answered": True,
            },
            "inputs": {
                "significance_outcome": sig_outcome,
                "limitation_outcome": lim_outcome,
                "acceptance_outcome": acc_outcome,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": success_margin_min,
                "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
                "limitation_primary_cause": str(limitation_summary.get("limitation_primary_cause", "")).strip(),
                "declaration_mapping_mismatch_if_external_success_and_scope_hold": declaration_mapping_mismatch_if_external_success_and_scope_hold,
            },
            "summary": {
                "all_criteria_satisfied": (preconditions_satisfied and scope_match)
                and (review_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": review_outcome,
            "reconciliation_status": reconciliation_status,
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
            "bridge_limitation_review_report": _ptr(limitation_path),
            "bridge_signal_margin_limitation_acceptance_review_report": _ptr(acceptance_path),
        },
        "non_claim_boundary": "Repository-local bridge interpretation-scope reconciliation review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge interpretation-scope reconciliation review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_reconciliation_review_20260422_v0.json",
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
    print(
        "qm_stat_rl10_discrete_transition_bridge_interpretation_scope_reconciliation_review_report: "
        f"{out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
