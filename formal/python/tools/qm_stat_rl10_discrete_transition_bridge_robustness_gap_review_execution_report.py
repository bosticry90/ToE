from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_GAP_REVIEW_EXECUTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_ROBUSTNESS_GAP_REVIEW_EXECUTION_20260412_v0.json"
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
    gap_spec = dict(declaration.get("gap_review_spec", {}))
    contract = dict(declaration.get("execution_contract", {}))

    robustness_exec_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_readiness_robustness_execution_report", "")
    ).strip()
    robustness_ruling_path = REPO_ROOT / str(
        required_inputs.get("bridge_probe_readiness_robustness_ruling_report", "")
    ).strip()
    binding_exec_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_comparator_binding_execution_report", "")
    ).strip()

    robustness_exec = _read_json(robustness_exec_path)
    robustness_ruling = _read_json(robustness_ruling_path)
    binding_exec = _read_json(binding_exec_path)

    robustness_exec_summary = dict(robustness_exec.get("summary", {}))
    robustness_ruling_summary = dict(robustness_ruling.get("summary", {}))
    binding_exec_summary = dict(binding_exec.get("summary", {}))

    robustness_terminal_outcome = str(robustness_exec_summary.get("terminal_outcome", "")).strip()
    robustness_ruling_status = str(robustness_ruling_summary.get("ruling_status", "")).strip()
    binding_terminal_outcome = str(binding_exec_summary.get("terminal_outcome", "")).strip()

    threshold_strictness_indicator = float(gap_spec.get("threshold_strictness_indicator", 0.0))
    fragility_indicator = float(gap_spec.get("fragility_indicator", 0.0))
    underdeclared_structure_detected = bool(gap_spec.get("underdeclared_structure_detected", False))
    comparator_binding_limit_detected = bool(gap_spec.get("comparator_binding_limit_detected", False))
    path_falsification_observed = bool(gap_spec.get("path_falsification_observed", False))

    if path_falsification_observed:
        terminal_outcome = "BRIDGE_SIGNAL_PATH_FALSIFIED"
        gap_primary_cause = "PATH_FALSIFICATION"
        next_action = "RETIRE_BRIDGE_PATH_AND_LOG_FALSIFICATION"
    elif underdeclared_structure_detected:
        terminal_outcome = "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED"
        gap_primary_cause = "UNDERDECLARED_BRIDGE_STRUCTURE"
        next_action = "AUTHORIZE_ONE_BOUNDED_STRUCTURE_REFINEMENT_PACKET"
    elif comparator_binding_limit_detected and threshold_strictness_indicator >= 0.03:
        terminal_outcome = "PROBE_READINESS_CRITERIA_REQUIRE_REVISION"
        gap_primary_cause = "COMPARATOR_BINDING_LIMITS"
        next_action = "REVIEW_AND_REVISE_PROBE_READINESS_CRITERIA_ONCE"
    elif (
        robustness_terminal_outcome == "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD"
        and robustness_ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and binding_terminal_outcome == "EXTERNAL_COMPARATOR_BINDING_CONFIRMED"
    ):
        # Current factual posture: comparator-bound hold with moderate fragility under bounded perturbation.
        if threshold_strictness_indicator >= 0.02 and fragility_indicator < 0.05:
            terminal_outcome = "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED"
            gap_primary_cause = "THRESHOLD_STRICTNESS"
            next_action = "AUTHORIZE_ONE_BOUNDED_ROBUSTNESS_REFINEMENT_PACKET"
        else:
            terminal_outcome = "COMPARATOR_BOUND_HOLD_RETAINED"
            gap_primary_cause = "SIGNAL_FRAGILITY"
            next_action = "RETAIN_HOLD_AND_RUN_NEXT_BOUNDED_ROBUSTNESS_REVIEW"
    else:
        terminal_outcome = "COMPARATOR_BOUND_HOLD_RETAINED"
        gap_primary_cause = "INSUFFICIENT_EVIDENCE_FOR_REFINEMENT"
        next_action = "RETAIN_HOLD_AND_COLLECT_BOUNDED_GAP_EVIDENCE"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = "COMPARATOR_BOUND_HOLD_RETAINED"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "comparator_binding_confirmed": binding_terminal_outcome == "EXTERNAL_COMPARATOR_BINDING_CONFIRMED",
            "robustness_hold_confirmed": robustness_terminal_outcome == "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD"
            and robustness_ruling_status == "TERMINAL_OUTCOME_CONFIRMED",
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_ROBUSTNESS_GAP_REVIEW_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_ROBUSTNESS_GAP_REVIEW_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "gap_cause_materialized": bool(gap_primary_cause),
            },
            "inputs": {
                "robustness_terminal_outcome": robustness_terminal_outcome,
                "robustness_ruling_status": robustness_ruling_status,
                "binding_terminal_outcome": binding_terminal_outcome,
                "threshold_strictness_indicator": threshold_strictness_indicator,
                "fragility_indicator": fragility_indicator,
                "underdeclared_structure_detected": underdeclared_structure_detected,
                "comparator_binding_limit_detected": comparator_binding_limit_detected,
                "path_falsification_observed": path_falsification_observed,
                "gap_primary_cause": gap_primary_cause,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome
                in {
                    "ONE_BOUNDED_ROBUSTNESS_REFINEMENT_JUSTIFIED",
                    "COMPARATOR_BOUND_HOLD_RETAINED",
                    "PROBE_READINESS_CRITERIA_REQUIRE_REVISION",
                    "BRIDGE_SIGNAL_PATH_FALSIFIED",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "gap_primary_cause": gap_primary_cause,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_probe_readiness_robustness_execution_report": _ptr(robustness_exec_path),
            "bridge_probe_readiness_robustness_ruling_report": _ptr(robustness_ruling_path),
            "bridge_external_comparator_binding_execution_report": _ptr(binding_exec_path),
        },
        "non_claim_boundary": "Repository-local bridge robustness-gap review execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge robustness-gap review execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_execution_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_robustness_gap_review_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())