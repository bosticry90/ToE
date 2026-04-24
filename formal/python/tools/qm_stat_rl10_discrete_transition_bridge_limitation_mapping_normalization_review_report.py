from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_REPORT_20260422_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_20260422_v0.json"
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
    policy = dict(declaration.get("normalization_policy", {}))
    contract = dict(declaration.get("normalization_contract", {}))

    significance_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_significance_adjudication_report", "")
    ).strip()
    limitation_path = REPO_ROOT / str(required_inputs.get("bridge_limitation_review_report", "")).strip()
    reconciliation_path = REPO_ROOT / str(
        required_inputs.get("bridge_interpretation_scope_reconciliation_review_report", "")
    ).strip()

    significance = _read_json(significance_path)
    limitation = _read_json(limitation_path)
    reconciliation = _read_json(reconciliation_path)

    significance_summary = dict(significance.get("summary", {}))
    limitation_summary = dict(limitation.get("summary", {}))
    reconciliation_summary = dict(reconciliation.get("summary", {}))

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()

    sig_outcome = str(significance_summary.get("adjudication_outcome", "")).strip()
    lim_outcome = str(limitation_summary.get("review_outcome", "")).strip()
    lim_primary_cause = str(limitation_summary.get("limitation_primary_cause", "")).strip()
    rec_outcome = str(reconciliation_summary.get("review_outcome", "")).strip()

    required_rec_outcome = str(
        policy.get("required_reconciliation_outcome", "INTERPRETATION_SCOPE_DECLARATION_INPUT_MISMATCH_CONFIRMED")
    ).strip()
    required_sig_outcome = str(
        policy.get("required_significance_outcome", "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE")
    ).strip()
    required_lim_outcome = str(
        policy.get("required_limitation_outcome", "LIMITATION_INTERPRETATION_SCOPE_HOLD")
    ).strip()
    required_lim_primary = str(
        policy.get(
            "required_limitation_primary_cause",
            "interpretation_scope_or_path_validity_not_sufficient_for_advancement",
        )
    ).strip()

    rec_matches = rec_outcome == required_rec_outcome
    sig_matches = sig_outcome == required_sig_outcome
    lim_matches = lim_outcome == required_lim_outcome
    lim_primary_matches = lim_primary_cause == required_lim_primary

    significance_comparator_id = str(significance_summary.get("external_comparator_id", "")).strip()
    significance_quantity_id = str(significance_summary.get("bridge_quantity_id", "")).strip()
    limitation_comparator_id = str(limitation_summary.get("external_comparator_id", "")).strip()
    limitation_quantity_id = str(limitation_summary.get("bridge_quantity_id", "")).strip()
    reconciliation_comparator_id = str(reconciliation_summary.get("external_comparator_id", "")).strip()
    reconciliation_quantity_id = str(reconciliation_summary.get("bridge_quantity_id", "")).strip()

    scope_match = (
        significance_comparator_id == expected_comparator_id
        and significance_quantity_id == expected_quantity_id
        and limitation_comparator_id == expected_comparator_id
        and limitation_quantity_id == expected_quantity_id
        and reconciliation_comparator_id == expected_comparator_id
        and reconciliation_quantity_id == expected_quantity_id
    )

    scope_guards_satisfied = bool(policy.get("not_a_new_hardening_cycle", True)) and bool(
        policy.get("no_scope_expansion", True)
    )

    preconditions_satisfied = (
        rec_matches and sig_matches and lim_matches and lim_primary_matches and scope_guards_satisfied
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))

    if not scope_match:
        normalization_outcome = "LIMITATION_MAPPING_NORMALIZATION_SCOPE_VIOLATION"
        next_action = "HOLD_AND_RESTORE_DECLARED_SEAM_BINDING"
    elif not preconditions_satisfied:
        normalization_outcome = "LIMITATION_MAPPING_NORMALIZATION_PRECONDITION_FAILED"
        next_action = "REPAIR_LIMITATION_MAPPING_NORMALIZATION_PRECONDITIONS"
    elif sig_outcome == lim_outcome:
        normalization_outcome = "LIMITATION_MAPPING_NORMALIZATION_NOT_REQUIRED"
        next_action = "RERUN_ACCEPTANCE_REVIEW_ON_CURRENT_MAPPING"
    else:
        normalization_outcome = "LIMITATION_MAPPING_NORMALIZATION_COMPLETED"
        next_action = "RERUN_ACCEPTANCE_REVIEW_ON_NORMALIZED_MAPPING_ONCE"

    if normalization_outcome not in allowed_outcomes:
        normalization_outcome = str(
            contract.get("default_outcome", "LIMITATION_MAPPING_NORMALIZATION_PRECONDITION_FAILED")
        ).strip()

    signal_margin = float(significance_summary.get("signal_margin", 0.0))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "reconciliation_outcome_matches_required": rec_matches,
            "significance_outcome_matches_required": sig_matches,
            "limitation_outcome_matches_required": lim_matches,
            "limitation_primary_cause_matches_required": lim_primary_matches,
            "scope_guards_satisfied": scope_guards_satisfied,
            "same_comparator_and_quantity_preserved": scope_match,
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_LIMITATION_MAPPING_NORMALIZATION_REVIEW_ONLY",
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_LIMITATION_MAPPING_NORMALIZATION_OUTCOME",
        },
        "objective_quality": {
            "criteria": {
                "preconditions_satisfied": preconditions_satisfied and scope_match,
                "allowed_outcome_materialized": normalization_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "normalization_answered": True,
            },
            "inputs": {
                "reconciliation_outcome": rec_outcome,
                "significance_outcome": sig_outcome,
                "limitation_outcome": lim_outcome,
                "limitation_primary_cause": lim_primary_cause,
                "normalized_acceptance_required_limitation_outcome": required_lim_outcome,
                "normalized_acceptance_required_limitation_primary_cause": required_lim_primary,
                "signal_margin": signal_margin,
            },
            "summary": {
                "all_criteria_satisfied": (preconditions_satisfied and scope_match)
                and (normalization_outcome in allowed_outcomes),
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "review_outcome": normalization_outcome,
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
            "bridge_interpretation_scope_reconciliation_review_report": _ptr(reconciliation_path),
        },
        "non_claim_boundary": "Repository-local limitation mapping normalization review report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge limitation mapping normalization review report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_limitation_mapping_normalization_review_20260422_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_limitation_mapping_normalization_review_report: "
        f"{out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
