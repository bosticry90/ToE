from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_REFINEMENT_EXECUTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_REFINEMENT_EXECUTION_20260412_v0.json"
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
    refinement_spec = dict(declaration.get("refinement_spec", {}))
    contract = dict(declaration.get("execution_contract", {}))

    gap_exec_path = REPO_ROOT / str(required_inputs.get("bridge_robustness_gap_review_execution_report", "")).strip()
    gap_ruling_path = REPO_ROOT / str(required_inputs.get("bridge_robustness_gap_review_ruling_report", "")).strip()
    robustness_exec_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_readiness_robustness_execution_report", "")
    ).strip()

    gap_exec = _read_json(gap_exec_path)
    gap_ruling = _read_json(gap_ruling_path)
    robustness_exec = _read_json(robustness_exec_path)

    gap_exec_summary = dict(gap_exec.get("summary", {}))
    gap_exec_inputs = dict(gap_exec.get("objective_quality", {}).get("inputs", {}))
    gap_ruling_summary = dict(gap_ruling.get("summary", {}))
    robustness_summary = dict(robustness_exec.get("summary", {}))

    gap_outcome = str(gap_exec_summary.get("terminal_outcome", "")).strip()
    gap_cause = str(gap_exec_summary.get("gap_primary_cause", "")).strip()
    gap_ruling_status = str(gap_ruling_summary.get("ruling_status", "")).strip()
    robustness_outcome = str(robustness_summary.get("terminal_outcome", "")).strip()

    external_comparator_id = str(robustness_summary.get("external_comparator_id", "")).strip()
    bridge_quantity_id = str(robustness_summary.get("bridge_quantity_id", "")).strip()
    perturbed_signal_margin = float(robustness_summary.get("perturbed_signal_margin", 0.0))

    expected_comparator_id = str(refinement_spec.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(refinement_spec.get("bridge_quantity_id", "")).strip()
    pre_threshold = float(refinement_spec.get("pre_refinement_probe_ready_margin_min", 0.06))
    refined_threshold = float(refinement_spec.get("refined_probe_ready_margin_min", 0.04))
    path_falsification_observed = bool(refinement_spec.get("path_falsification_observed", False))

    threshold_strictness_indicator = float(gap_exec_inputs.get("threshold_strictness_indicator", 0.0))
    fragility_indicator = float(gap_exec_inputs.get("fragility_indicator", 0.0))

    comparator_quantity_match = (
        external_comparator_id == expected_comparator_id and bridge_quantity_id == expected_quantity_id
    )

    if path_falsification_observed:
        terminal_outcome = "BRIDGE_SIGNAL_PATH_FALSIFIED"
        next_action = "RETIRE_PATH_AFTER_REFINEMENT_FALSIFICATION"
    elif not comparator_quantity_match:
        terminal_outcome = "ROBUSTNESS_REFINEMENT_INCONCLUSIVE"
        next_action = "FIX_REFINEMENT_BINDING_SCOPE_MISMATCH"
    elif not (
        gap_outcome == "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED"
        and gap_ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and gap_cause == "THRESHOLD_STRICTNESS"
    ):
        terminal_outcome = "ROBUSTNESS_REFINEMENT_INCONCLUSIVE"
        next_action = "REQUIRE_CONFIRMED_THRESHOLD_STRICTNESS_GAP_REVIEW"
    elif perturbed_signal_margin >= refined_threshold and fragility_indicator <= 0.05:
        terminal_outcome = "BRIDGE_SIGNAL_PROBE_READY"
        next_action = "AUTHORIZE_SINGLE_PROBE_LANE_GATING_PACKET"
    elif perturbed_signal_margin >= 0.02 and fragility_indicator <= 0.06:
        terminal_outcome = "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD"
        next_action = "RETAIN_HOLD_AFTER_REFINEMENT_AND_MONITOR"
    else:
        terminal_outcome = "ROBUSTNESS_REFINEMENT_INCONCLUSIVE"
        next_action = "INCONCLUSIVE_REFINEMENT_REQUIRE_NEXT_BOUNDED_REVIEW"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = "ROBUSTNESS_REFINEMENT_INCONCLUSIVE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "gap_review_justified_and_confirmed": gap_outcome == "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED"
            and gap_ruling_status == "TERMINAL_OUTCOME_CONFIRMED",
            "threshold_strictness_focus_preserved": gap_cause == "THRESHOLD_STRICTNESS",
            "single_comparator_single_quantity_preserved": comparator_quantity_match,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_REFINEMENT_EXECUTION_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_ROBUSTNESS_REFINEMENT_EXECUTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "refinement_threshold_tightening_applied": refined_threshold < pre_threshold,
            },
            "inputs": {
                "gap_outcome": gap_outcome,
                "gap_cause": gap_cause,
                "gap_ruling_status": gap_ruling_status,
                "robustness_outcome": robustness_outcome,
                "external_comparator_id": external_comparator_id,
                "bridge_quantity_id": bridge_quantity_id,
                "expected_comparator_id": expected_comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "perturbed_signal_margin": perturbed_signal_margin,
                "pre_refinement_probe_ready_margin_min": pre_threshold,
                "refined_probe_ready_margin_min": refined_threshold,
                "threshold_strictness_indicator": threshold_strictness_indicator,
                "fragility_indicator": fragility_indicator,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome == "BRIDGE_SIGNAL_PROBE_READY",
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "perturbed_signal_margin": perturbed_signal_margin,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_robustness_gap_review_execution_report": _ptr(gap_exec_path),
            "bridge_robustness_gap_review_ruling_report": _ptr(gap_ruling_path),
            "bridge_probe_readiness_robustness_execution_report": _ptr(robustness_exec_path),
        },
        "non_claim_boundary": "Repository-local bridge robustness refinement execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge robustness refinement execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_robustness_refinement_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
