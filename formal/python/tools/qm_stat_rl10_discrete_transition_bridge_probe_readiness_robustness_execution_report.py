from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_READINESS_ROBUSTNESS_EXECUTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_READINESS_ROBUSTNESS_EXECUTION_20260412_v0.json"
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
    robustness_spec = dict(declaration.get("robustness_spec", {}))
    contract = dict(declaration.get("execution_contract", {}))

    binding_exec_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_comparator_binding_execution_report", "")
    ).strip()
    binding_ruling_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_comparator_binding_ruling_report", "")
    ).strip()

    binding_exec = _read_json(binding_exec_path)
    binding_ruling = _read_json(binding_ruling_path)

    binding_exec_summary = dict(binding_exec.get("summary", {}))
    binding_ruling_summary = dict(binding_ruling.get("summary", {}))

    binding_outcome = str(binding_exec_summary.get("terminal_outcome", "")).strip()
    ruling_status = str(binding_ruling_summary.get("ruling_status", "")).strip()
    ruling_outcome = str(binding_ruling_summary.get("terminal_outcome", "")).strip()

    comparator_id = str(binding_exec_summary.get("external_comparator_id", "")).strip()
    quantity_id = str(binding_exec_summary.get("bridge_quantity_id", "")).strip()
    expected_comparator_id = str(robustness_spec.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(robustness_spec.get("bridge_quantity_id", "")).strip()

    baseline_signal_margin = float(robustness_spec.get("baseline_signal_margin", 0.0))
    perturbation_delta = float(robustness_spec.get("perturbation_delta", 0.0))
    probe_ready_margin_min = float(robustness_spec.get("probe_ready_margin_min", 0.06))
    hold_margin_min = float(robustness_spec.get("hold_margin_min", 0.02))
    path_falsification_observed = bool(robustness_spec.get("path_falsification_observed", False))

    perturbed_signal_margin = baseline_signal_margin - perturbation_delta

    comparator_bound = (
        binding_outcome in {"EXTERNAL_COMPARATOR_BINDING_CONFIRMED", "BRIDGE_SIGNAL_PROBE_READY"}
        and ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and ruling_outcome == binding_outcome
        and comparator_id == expected_comparator_id
        and quantity_id == expected_quantity_id
    )

    if path_falsification_observed:
        terminal_outcome = "BRIDGE_SIGNAL_PATH_FALSIFIED"
        next_action = "RETIRE_PATH_AND_RECORD_ROBUSTNESS_FALSIFICATION"
    elif comparator_bound and perturbed_signal_margin >= probe_ready_margin_min:
        terminal_outcome = "BRIDGE_SIGNAL_PROBE_READY"
        next_action = "AUTHORIZE_SINGLE_PROBE_LANE_PACKET"
    elif comparator_bound and perturbed_signal_margin >= hold_margin_min:
        terminal_outcome = "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD"
        next_action = "HOLD_PROBE_LAUNCH_AND_COLLECT_BOUNDED_ROBUSTNESS_EVIDENCE"
    elif comparator_bound:
        terminal_outcome = "BRIDGE_SIGNAL_ROBUSTNESS_FAILURE"
        next_action = "REPAIR_ROBUSTNESS_FAILURE_BEFORE_PROBE_LANE"
    else:
        terminal_outcome = "BRIDGE_SIGNAL_ROBUSTNESS_FAILURE"
        next_action = "REPAIR_BINDING_PRECONDITIONS_BEFORE_ROBUSTNESS_REVIEW"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = "BRIDGE_SIGNAL_COMPARATOR_BOUND_BUT_HOLD"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "comparator_bound_and_confirmed": comparator_bound,
            "perturbation_applied": perturbation_delta >= 0.0,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_ROBUSTNESS_EXECUTION_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_PROBE_READINESS_ROBUSTNESS_EXECUTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "single_comparator_single_quantity_enforced": comparator_id == expected_comparator_id
                and quantity_id == expected_quantity_id,
            },
            "inputs": {
                "binding_outcome": binding_outcome,
                "ruling_status": ruling_status,
                "ruling_outcome": ruling_outcome,
                "expected_comparator_id": expected_comparator_id,
                "actual_comparator_id": comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "actual_quantity_id": quantity_id,
                "baseline_signal_margin": baseline_signal_margin,
                "perturbation_delta": perturbation_delta,
                "perturbed_signal_margin": perturbed_signal_margin,
                "probe_ready_margin_min": probe_ready_margin_min,
                "hold_margin_min": hold_margin_min,
                "path_falsification_observed": path_falsification_observed,
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
            "bridge_external_comparator_binding_execution_report": _ptr(binding_exec_path),
            "bridge_external_comparator_binding_ruling_report": _ptr(binding_ruling_path),
        },
        "non_claim_boundary": "Repository-local bridge probe-readiness robustness execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge probe-readiness robustness execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_execution_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_probe_readiness_robustness_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())