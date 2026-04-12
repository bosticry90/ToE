from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_EXECUTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_PROBE_EXECUTION_20260412_v0.json"
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
    probe_spec = dict(declaration.get("probe_spec", {}))
    contract = dict(declaration.get("execution_contract", {}))

    refinement_exec_path = REPO_ROOT / str(
        required_inputs.get("bridge_robustness_refinement_execution_report", "")
    ).strip()
    refinement_ruling_path = REPO_ROOT / str(
        required_inputs.get("bridge_robustness_refinement_ruling_report", "")
    ).strip()

    refinement_exec = _read_json(refinement_exec_path)
    refinement_ruling = _read_json(refinement_ruling_path)

    refinement_exec_summary = dict(refinement_exec.get("summary", {}))
    refinement_ruling_summary = dict(refinement_ruling.get("summary", {}))

    refinement_outcome = str(refinement_exec_summary.get("terminal_outcome", "")).strip()
    refinement_ruling_status = str(refinement_ruling_summary.get("ruling_status", "")).strip()

    expected_comparator_id = str(probe_spec.get("external_comparator_id", "")).strip()
    expected_quantity_id = str(probe_spec.get("bridge_quantity_id", "")).strip()
    comparator_id = str(refinement_exec_summary.get("external_comparator_id", "")).strip()
    quantity_id = str(refinement_exec_summary.get("bridge_quantity_id", "")).strip()

    signal_strength = float(probe_spec.get("probe_signal_strength", 0.0))
    signal_threshold = float(probe_spec.get("probe_signal_threshold", 0.0))
    discrimination_threshold = float(probe_spec.get("probe_discrimination_threshold", 0.02))
    path_falsification_observed = bool(probe_spec.get("path_falsification_observed", False))

    signal_margin = signal_strength - signal_threshold

    scope_match = comparator_id == expected_comparator_id and quantity_id == expected_quantity_id

    if path_falsification_observed:
        terminal_outcome = "PROBE_PATH_FALSIFIED"
        next_action = "RETIRE_PROBE_PATH"
    elif (
        refinement_outcome == "BRIDGE_SIGNAL_PROBE_READY"
        and refinement_ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and scope_match
        and signal_margin >= discrimination_threshold
    ):
        terminal_outcome = "PROBE_SIGNAL_CONFIRMED"
        next_action = "PREPARE_SINGLE_PROBE_SIGNIFICANCE_ADJUDICATION"
    elif (
        refinement_outcome == "BRIDGE_SIGNAL_PROBE_READY"
        and refinement_ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and scope_match
        and signal_margin >= 0.0
    ):
        terminal_outcome = "PROBE_SIGNAL_NONDISCRIMINATIVE"
        next_action = "HOLD_PROBE_AND_IMPROVE_DISCRIMINATION"
    else:
        terminal_outcome = "PROBE_SIGNAL_INCONCLUSIVE"
        next_action = "REVIEW_PROBE_EXECUTION_PRECONDITIONS"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = "PROBE_SIGNAL_INCONCLUSIVE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "refinement_probe_ready_confirmed": refinement_outcome == "BRIDGE_SIGNAL_PROBE_READY"
            and refinement_ruling_status == "TERMINAL_OUTCOME_CONFIRMED",
            "same_comparator_and_quantity_preserved": scope_match,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_PROBE_EXECUTION_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_PROBE_EXECUTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "bounded_discrimination_check_applied": discrimination_threshold >= 0.0,
            },
            "inputs": {
                "refinement_outcome": refinement_outcome,
                "refinement_ruling_status": refinement_ruling_status,
                "expected_comparator_id": expected_comparator_id,
                "actual_comparator_id": comparator_id,
                "expected_quantity_id": expected_quantity_id,
                "actual_quantity_id": quantity_id,
                "probe_signal_strength": signal_strength,
                "probe_signal_threshold": signal_threshold,
                "signal_margin": signal_margin,
                "probe_discrimination_threshold": discrimination_threshold,
                "path_falsification_observed": path_falsification_observed,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in {"PROBE_SIGNAL_CONFIRMED", "PROBE_SIGNAL_NONDISCRIMINATIVE"},
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "external_comparator_id": expected_comparator_id,
            "bridge_quantity_id": expected_quantity_id,
            "signal_margin": signal_margin,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_robustness_refinement_execution_report": _ptr(refinement_exec_path),
            "bridge_robustness_refinement_ruling_report": _ptr(refinement_ruling_path),
        },
        "non_claim_boundary": "Repository-local bridge probe execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge probe execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_probe_execution_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_probe_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
