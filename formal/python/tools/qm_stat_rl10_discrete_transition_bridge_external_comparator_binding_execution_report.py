from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_20260412_v0.json"
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
    binding_spec = dict(declaration.get("binding_spec", {}))
    contract = dict(declaration.get("execution_contract", {}))

    adjudication_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_comparability_adjudication_report", "")
    ).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("bridge_first_test_execution_report", "")).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("qm_stat_single_baseline_comparator_report", "")).strip()

    adjudication = _read_json(adjudication_path)
    execution = _read_json(execution_path)
    comparator = _read_json(comparator_path)

    adjudication_summary = dict(adjudication.get("summary", {}))
    execution_summary = dict(execution.get("summary", {}))
    comparator_summary = dict(comparator.get("summary", {}))

    adjudication_outcome = str(adjudication_summary.get("adjudication_outcome", "")).strip()
    bridge_execution_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    comparator_status = str(comparator_summary.get("comparator_status", "")).strip()

    expected_comparator_id = str(binding_spec.get("external_comparator_id", "")).strip()
    expected_comparator_schema = str(binding_spec.get("external_comparator_schema", "")).strip()
    expected_quantity_id = str(binding_spec.get("bridge_quantity_id", "")).strip()

    actual_comparator_id = str(comparator_summary.get("baseline_id", "")).strip()
    actual_comparator_schema = str(comparator_summary.get("baseline_schema", "")).strip()
    actual_quantity_id = str(execution_summary.get("test_observable_id", "")).strip()

    signal_strength = float(execution_summary.get("observed_signal_strength", 0.0))
    signal_threshold = float(execution_summary.get("signal_threshold", 0.0))
    signal_margin = signal_strength - signal_threshold

    binding_success_margin_min = float(binding_spec.get("binding_success_margin_min", 0.06))
    probe_ready_margin_min = float(binding_spec.get("probe_ready_margin_min", 0.10))
    partial_hold_margin_min = float(binding_spec.get("partial_hold_margin_min", 0.03))

    path_falsified = bridge_execution_outcome == "BRIDGE_SEAM_PATH_FALSIFIED"
    comparator_match = (
        comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
        and actual_comparator_id == expected_comparator_id
        and actual_comparator_schema == expected_comparator_schema
    )
    quantity_match = actual_quantity_id == expected_quantity_id

    if path_falsified:
        terminal_outcome = "BRIDGE_SIGNAL_PATH_FALSIFIED"
        next_action = "RETIRE_BINDING_PATH_AND_LOG_FALSIFICATION"
    elif (
        adjudication_outcome in {"BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CONFIRMED", "BRIDGE_SIGNAL_PROBE_READY"}
        and comparator_match
        and quantity_match
        and signal_margin >= probe_ready_margin_min
    ):
        terminal_outcome = "BRIDGE_SIGNAL_PROBE_READY"
        next_action = "AUTHORIZE_ONE_BOUNDED_EXTERNAL_PROBE_EXECUTION"
    elif (
        adjudication_outcome in {"BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CONFIRMED", "BRIDGE_SIGNAL_PROBE_READY"}
        and comparator_match
        and quantity_match
        and signal_margin >= binding_success_margin_min
    ):
        terminal_outcome = "EXTERNAL_COMPARATOR_BINDING_CONFIRMED"
        next_action = "PREPARE_BINDING_RULING_AND_SINGLE_FOLLOWUP_PACKET"
    elif signal_margin >= partial_hold_margin_min and comparator_match and quantity_match:
        terminal_outcome = "COMPARATOR_BINDING_PARTIAL_HOLD"
        next_action = "HOLD_AND_TIGHTEN_BINDING_THRESHOLD_EVIDENCE"
    else:
        terminal_outcome = "COMPARATOR_BINDING_PARTIAL_HOLD"
        next_action = "HOLD_AND_REVIEW_COMPARATOR_BINDING_PRECONDITIONS"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = "COMPARATOR_BINDING_PARTIAL_HOLD"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "adjudication_supports_binding": adjudication_outcome
            in {"BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CONFIRMED", "BRIDGE_SIGNAL_PROBE_READY"},
            "comparator_match": comparator_match,
            "quantity_match": quantity_match,
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_BINDING_EXECUTION_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "single_comparator_bound": comparator_match,
            },
            "inputs": {
                "adjudication_outcome": adjudication_outcome,
                "bridge_execution_outcome": bridge_execution_outcome,
                "expected_comparator_id": expected_comparator_id,
                "actual_comparator_id": actual_comparator_id,
                "expected_comparator_schema": expected_comparator_schema,
                "actual_comparator_schema": actual_comparator_schema,
                "expected_quantity_id": expected_quantity_id,
                "actual_quantity_id": actual_quantity_id,
                "signal_strength": signal_strength,
                "signal_threshold": signal_threshold,
                "signal_margin": signal_margin,
                "binding_success_margin_min": binding_success_margin_min,
                "probe_ready_margin_min": probe_ready_margin_min,
                "partial_hold_margin_min": partial_hold_margin_min,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome
                in {"EXTERNAL_COMPARATOR_BINDING_CONFIRMED", "BRIDGE_SIGNAL_PROBE_READY"},
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
            "bridge_external_comparability_adjudication_report": _ptr(adjudication_path),
            "bridge_first_test_execution_report": _ptr(execution_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
        },
        "non_claim_boundary": "Repository-local bridge external comparator binding execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge external comparator binding execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())