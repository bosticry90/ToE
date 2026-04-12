from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARABILITY_ADJUDICATION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_EXTERNAL_COMPARABILITY_ADJUDICATION_20260412_v0.json"
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
    comparator_binding = dict(declaration.get("comparator_binding", {}))
    contract = dict(declaration.get("adjudication_contract", {}))

    interpretation_path = REPO_ROOT / str(required_inputs.get("bridge_signal_interpretation_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("bridge_first_test_execution_report", "")).strip()
    ruling_path = REPO_ROOT / str(required_inputs.get("bridge_first_test_ruling_report", "")).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("qm_stat_single_baseline_comparator_report", "")).strip()

    interpretation = _read_json(interpretation_path)
    execution = _read_json(execution_path)
    ruling = _read_json(ruling_path)
    comparator = _read_json(comparator_path)

    interpretation_summary = dict(interpretation.get("summary", {}))
    execution_summary = dict(execution.get("summary", {}))
    ruling_summary = dict(ruling.get("summary", {}))
    comparator_summary = dict(comparator.get("summary", {}))

    interpretation_outcome = str(interpretation_summary.get("interpretation_outcome", "")).strip()
    execution_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    ruling_outcome = str(ruling_summary.get("terminal_outcome", "")).strip()
    ruling_status = str(ruling_summary.get("ruling_status", "")).strip()

    comparator_id = str(comparator_summary.get("baseline_id", "")).strip()
    comparator_schema = str(comparator_summary.get("baseline_schema", "")).strip()
    comparator_status = str(comparator_summary.get("comparator_status", "")).strip()

    expected_comparator_id = str(comparator_binding.get("external_comparator_id", "")).strip()
    expected_comparator_schema = str(comparator_binding.get("external_comparator_schema", "")).strip()
    expected_quantity_id = str(comparator_binding.get("comparable_quantity_id", "")).strip()

    observed_quantity_id = str(execution_summary.get("test_observable_id", "")).strip()
    signal_strength = float(execution_summary.get("observed_signal_strength", 0.0))
    signal_threshold = float(execution_summary.get("signal_threshold", 0.0))
    signal_margin = signal_strength - signal_threshold

    confirm_margin = float(comparator_binding.get("confirmation_signal_margin_min", 0.05))
    probe_ready_margin = float(comparator_binding.get("probe_ready_signal_margin_min", 0.10))

    comparator_bound = (
        comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
        and comparator_id == expected_comparator_id
        and comparator_schema == expected_comparator_schema
    )
    quantity_comparable = observed_quantity_id == expected_quantity_id
    path_falsified = execution_outcome == "BRIDGE_SEAM_PATH_FALSIFIED" or ruling_outcome == "BRIDGE_SEAM_PATH_FALSIFIED"

    if path_falsified:
        adjudication_outcome = "BRIDGE_SIGNAL_PATH_FALSIFIED"
        next_action = "RETIRE_BRIDGE_PATH_AND_RECORD_FALSIFICATION"
    elif (
        interpretation_outcome == "BRIDGE_SIGNAL_PROBE_READY"
        and comparator_bound
        and quantity_comparable
        and ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and signal_margin >= probe_ready_margin
    ):
        adjudication_outcome = "BRIDGE_SIGNAL_PROBE_READY"
        next_action = "AUTHORIZE_ONE_BOUNDED_EXTERNAL_PROBE_PACKET"
    elif (
        interpretation_outcome == "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE"
        and comparator_bound
        and quantity_comparable
        and ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
        and signal_margin >= confirm_margin
    ):
        adjudication_outcome = "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CONFIRMED"
        next_action = "PREPARE_EXTERNAL_COMPARATOR_BINDING_EXECUTION_PACKET"
    else:
        adjudication_outcome = "BRIDGE_SIGNAL_CANDIDATE_ONLY_HOLD"
        next_action = "HOLD_CANDIDATE_STATUS_AND_TIGHTEN_BOUNDED_SIGNAL_EVIDENCE"

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    if adjudication_outcome not in allowed_outcomes:
        adjudication_outcome = str(contract.get("default_outcome", "BRIDGE_SIGNAL_CANDIDATE_ONLY_HOLD")).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "comparator_bound": comparator_bound,
            "quantity_comparable": quantity_comparable,
            "signal_produced_and_confirmed": execution_outcome == "BRIDGE_SEAM_SIGNAL_PRODUCED"
            and ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
            and ruling_outcome == "BRIDGE_SEAM_SIGNAL_PRODUCED",
            "single_terminal_outcome_rule_declared": str(contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_ADJUDICATION_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_EXTERNAL_COMPARABILITY_ADJUDICATION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": adjudication_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "comparator_binding_explicit": bool(expected_comparator_id and expected_comparator_schema),
            },
            "inputs": {
                "interpretation_outcome": interpretation_outcome,
                "execution_outcome": execution_outcome,
                "ruling_status": ruling_status,
                "ruling_outcome": ruling_outcome,
                "expected_comparator_id": expected_comparator_id,
                "actual_comparator_id": comparator_id,
                "expected_comparator_schema": expected_comparator_schema,
                "actual_comparator_schema": comparator_schema,
                "expected_quantity_id": expected_quantity_id,
                "observed_quantity_id": observed_quantity_id,
                "signal_margin": signal_margin,
                "confirmation_signal_margin_min": confirm_margin,
                "probe_ready_signal_margin_min": probe_ready_margin,
            },
            "summary": {
                "all_criteria_satisfied": adjudication_outcome
                in {"BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CONFIRMED", "BRIDGE_SIGNAL_PROBE_READY"},
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "adjudication_outcome": adjudication_outcome,
            "external_comparator_id": expected_comparator_id,
            "comparable_quantity_id": expected_quantity_id,
            "signal_margin": signal_margin,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_signal_interpretation_report": _ptr(interpretation_path),
            "bridge_first_test_execution_report": _ptr(execution_path),
            "bridge_first_test_ruling_report": _ptr(ruling_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
        },
        "non_claim_boundary": "Repository-local bridge external-comparability adjudication report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge external-comparability adjudication report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_external_comparability_adjudication_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_external_comparability_adjudication_report: "
        f"adjudication_outcome={payload['summary']['adjudication_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())