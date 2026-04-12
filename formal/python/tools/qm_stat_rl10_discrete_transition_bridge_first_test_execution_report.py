from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_EXECUTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_EXECUTION_20260412_v0.json"
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


def _decide_terminal_outcome(
    *,
    packet_terminal_outcome: str,
    bridge_ready: bool,
    comparator_ready: bool,
    falsification_observed: bool,
    undeclared_structure_needed: list[str],
    signal_strength: float,
    signal_threshold: float,
) -> str:
    if undeclared_structure_needed:
        return "BRIDGE_SEAM_REQUIRES_FURTHER_DECLARED_STRUCTURE"
    if falsification_observed:
        return "BRIDGE_SEAM_PATH_FALSIFIED"
    if not bridge_ready or not comparator_ready:
        return "BRIDGE_SEAM_INTERNAL_ONLY"
    if packet_terminal_outcome != "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE":
        return "BRIDGE_SEAM_INTERNAL_ONLY"
    if signal_strength >= signal_threshold:
        return "BRIDGE_SEAM_SIGNAL_PRODUCED"
    return "BRIDGE_SEAM_INTERNAL_ONLY"


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    execution_payload = dict(declaration.get("execution_payload", {}))
    execution_contract = dict(declaration.get("execution_contract", {}))

    packet_path = REPO_ROOT / str(required_inputs.get("bridge_first_test_packet_report", "")).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("qm_stat_single_baseline_comparator_report", "")).strip()

    packet = _read_json(packet_path)
    comparator = _read_json(comparator_path)

    packet_summary = dict(packet.get("summary", {}))
    packet_criteria = dict(packet.get("criteria", {}))
    comparator_summary = dict(comparator.get("summary", {}))

    packet_terminal_outcome = str(packet_summary.get("terminal_outcome", "")).strip()
    bridge_ready = bool(packet_criteria.get("bridge_observable_ready", False))
    transition_coherent = bool(packet_criteria.get("transition_structure_coherent", False))
    governance_ok = bool(packet_criteria.get("governance_boundary_preserved", False))

    comparator_ready = (
        str(comparator_summary.get("comparator_status", "")).strip() == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
        and str(comparator_summary.get("baseline_id", "")).strip() == "OV-RL-10"
    )

    observable_id = str(execution_payload.get("test_observable_id", "")).strip()
    signal_threshold = float(execution_payload.get("signal_threshold", 0.0))
    signal_strength = float(execution_payload.get("observed_signal_strength", 0.0))
    falsification_observed = bool(execution_payload.get("falsification_observed", False))
    undeclared_structure_needed = list(execution_payload.get("undeclared_structure_needed", []))

    terminal_outcome = _decide_terminal_outcome(
        packet_terminal_outcome=packet_terminal_outcome,
        bridge_ready=bridge_ready and transition_coherent and governance_ok,
        comparator_ready=comparator_ready,
        falsification_observed=falsification_observed,
        undeclared_structure_needed=undeclared_structure_needed,
        signal_strength=signal_strength,
        signal_threshold=signal_threshold,
    )

    if terminal_outcome == "BRIDGE_SEAM_SIGNAL_PRODUCED":
        next_action = "PROMOTE_TO_DISCOVERY_REVIEW_WITH_SINGLE_BOUNDED_SIGNAL_PACKET"
    elif terminal_outcome == "BRIDGE_SEAM_INTERNAL_ONLY":
        next_action = "HOLD_AS_INTERNAL_ONLY_AND_DO_NOT_REOPEN_CYCLE11_QM_STAT_PATH"
    elif terminal_outcome == "BRIDGE_SEAM_PATH_FALSIFIED":
        next_action = "RETIRE_THIS_BRIDGE_SEAM_PATH_AND_RECORD_FALSIFICATION"
    else:
        next_action = "DECLARE_REQUIRED_STRUCTURE_AND_RETRY_WITH_NEW_BOUNDED_PACKET"

    allowed_outcomes = set(execution_contract.get("allowed_outcomes", []))

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "first_test_packet_executable": packet_terminal_outcome == "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE",
            "transition_structure_coherent": transition_coherent,
            "bridge_observable_ready": bridge_ready,
            "governance_boundary_preserved": governance_ok,
            "single_baseline_comparator_ready": comparator_ready,
            "single_terminal_outcome_rule_declared": str(execution_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_TERMINAL_OUTCOME",
            "no_loop_rule_declared": str(execution_contract.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_SEAM_FIRST_TEST_EXECUTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_terminal_outcome_materialized": True,
                "execution_payload_bound": bool(observable_id),
                "bounded_signal_threshold_used": signal_threshold >= 0.0,
            },
            "inputs": {
                "packet_terminal_outcome": packet_terminal_outcome,
                "observable_id": observable_id,
                "signal_threshold": signal_threshold,
                "observed_signal_strength": signal_strength,
                "falsification_observed": falsification_observed,
                "undeclared_structure_needed": undeclared_structure_needed,
                "allowed_outcomes": sorted(allowed_outcomes),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome == "BRIDGE_SEAM_SIGNAL_PRODUCED",
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "test_observable_id": observable_id,
            "signal_threshold": signal_threshold,
            "observed_signal_strength": signal_strength,
            "falsification_observed": falsification_observed,
            "undeclared_structure_needed": undeclared_structure_needed,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_first_test_packet_report": _ptr(packet_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
        },
        "non_claim_boundary": "Repository-local bridge seam first-test execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge seam first-test execution report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_first_test_execution_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_first_test_execution_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())