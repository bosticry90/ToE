from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_SIGNIFICANCE_ADJUDICATION_REPORT_20260412_v0"
)
_FP_TOLERANCE = 1e-9

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_SIGNIFICANCE_ADJUDICATION_20260412_v0.json"
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
    significance_policy = dict(declaration.get("significance_policy", {}))
    contract = dict(declaration.get("adjudication_contract", {}))

    probe_execution_path = REPO_ROOT / str(required_inputs.get("bridge_probe_execution_report", "")).strip()
    probe_ruling_path = REPO_ROOT / str(required_inputs.get("bridge_probe_ruling_report", "")).strip()

    probe_execution = _read_json(probe_execution_path)
    probe_ruling = _read_json(probe_ruling_path)

    execution_summary = dict(probe_execution.get("summary", {}))
    ruling_summary = dict(probe_ruling.get("summary", {}))

    execution_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    ruling_outcome = str(ruling_summary.get("terminal_outcome", "")).strip()
    ruling_status = str(ruling_summary.get("ruling_status", "")).strip()

    expected_comparator_id = str(seam_scope.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(seam_scope.get("bridge_quantity_id", "")).strip()
    observed_comparator_id = str(execution_summary.get("external_comparator_id", "")).strip()
    observed_quantity_id = str(execution_summary.get("bridge_quantity_id", "")).strip()

    signal_margin = float(execution_summary.get("signal_margin", 0.0))
    success_margin_min = float(significance_policy.get("external_path_success_signal_margin_min", 0.05))
    limited_margin_min = float(significance_policy.get("confirmed_but_limited_signal_margin_min", 0.02))
    one_more_cycle_margin_min = float(significance_policy.get("one_more_cycle_signal_margin_min", 0.0))

    comparator_repeatability_confirmed = bool(significance_policy.get("comparator_repeatability_confirmed", False))
    cross_probe_consistency_confirmed = bool(significance_policy.get("cross_probe_consistency_confirmed", False))

    scope_match = (
        observed_comparator_id == expected_comparator_id
        and observed_quantity_id == expected_quantity_id
    )

    path_hold_triggered = (
        execution_outcome == "PROBE_PATH_FALSIFIED"
        or ruling_outcome == "PROBE_PATH_FALSIFIED"
        or ruling_status != "TERMINAL_OUTCOME_CONFIRMED"
        or not scope_match
    )

    if path_hold_triggered:
        adjudication_outcome = "PROBE_SIGNAL_PATH_HOLD"
        next_action = "HOLD_BRIDGE_SEAM_AND_RESOLVE_SCOPE_OR_PATH_VALIDITY_GAPS"
    elif (
        execution_outcome == "PROBE_SIGNAL_CONFIRMED"
        and ruling_outcome == "PROBE_SIGNAL_CONFIRMED"
        and signal_margin >= success_margin_min - _FP_TOLERANCE
        and comparator_repeatability_confirmed
        and cross_probe_consistency_confirmed
    ):
        adjudication_outcome = "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE"
        next_action = "KEEP_BRIDGE_SEAM_PRIMARY_AND_PREPARE_EXTERNAL_PATH_PROMOTION_REVIEW"
    elif (
        execution_outcome == "PROBE_SIGNAL_CONFIRMED"
        and ruling_outcome == "PROBE_SIGNAL_CONFIRMED"
        and signal_margin >= limited_margin_min - _FP_TOLERANCE
    ):
        adjudication_outcome = "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED"
        next_action = "KEEP_BRIDGE_SEAM_PRIMARY_WITH_BOUNDED_LIMITATION_DISCIPLINE"
    elif (
        execution_outcome in {"PROBE_SIGNAL_NONDISCRIMINATIVE", "PROBE_SIGNAL_INCONCLUSIVE"}
        and ruling_outcome in {"PROBE_SIGNAL_NONDISCRIMINATIVE", "PROBE_SIGNAL_INCONCLUSIVE"}
        and signal_margin >= one_more_cycle_margin_min - _FP_TOLERANCE
    ):
        adjudication_outcome = "PROBE_SIGNAL_REQUIRES_ONE_MORE_BOUNDED_COMPARATOR_CYCLE"
        next_action = "AUTHORIZE_ONE_ADDITIONAL_BOUNDED_COMPARATOR_CYCLE"
    else:
        adjudication_outcome = str(contract.get("default_outcome", "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED")).strip()
        next_action = "KEEP_BRIDGE_SEAM_PRIMARY_WITH_BOUNDED_LIMITATION_DISCIPLINE"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if adjudication_outcome not in allowed_outcomes:
        adjudication_outcome = str(contract.get("default_outcome", "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED")).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "probe_signal_confirmed_inbound": execution_outcome == "PROBE_SIGNAL_CONFIRMED"
            and ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
            and ruling_outcome == "PROBE_SIGNAL_CONFIRMED",
            "same_comparator_and_quantity_preserved": scope_match,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_PROBE_SIGNIFICANCE_ADJUDICATION_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_PROBE_SIGNIFICANCE_ADJUDICATION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": adjudication_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "bounded_significance_policy_applied": success_margin_min >= limited_margin_min >= one_more_cycle_margin_min,
            },
            "inputs": {
                "execution_outcome": execution_outcome,
                "ruling_status": ruling_status,
                "ruling_outcome": ruling_outcome,
                "expected_comparator_id": expected_comparator_id,
                "observed_comparator_id": observed_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
                "signal_margin": signal_margin,
                "external_path_success_signal_margin_min": success_margin_min,
                "confirmed_but_limited_signal_margin_min": limited_margin_min,
                "one_more_cycle_signal_margin_min": one_more_cycle_margin_min,
                "comparator_repeatability_confirmed": comparator_repeatability_confirmed,
                "cross_probe_consistency_confirmed": cross_probe_consistency_confirmed,
            },
            "summary": {
                "all_criteria_satisfied": adjudication_outcome
                in {
                    "PROBE_SIGNAL_EXTERNAL_PATH_SUCCESS_CANDIDATE",
                    "PROBE_SIGNAL_CONFIRMED_BUT_LIMITED",
                    "PROBE_SIGNAL_REQUIRES_ONE_MORE_BOUNDED_COMPARATOR_CYCLE",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "adjudication_outcome": adjudication_outcome,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin": signal_margin,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_probe_execution_report": _ptr(probe_execution_path),
            "bridge_probe_ruling_report": _ptr(probe_ruling_path),
        },
        "non_claim_boundary": "Repository-local bridge probe significance adjudication report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge probe significance adjudication report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_probe_significance_adjudication_report: "
        f"adjudication_outcome={payload['summary']['adjudication_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
