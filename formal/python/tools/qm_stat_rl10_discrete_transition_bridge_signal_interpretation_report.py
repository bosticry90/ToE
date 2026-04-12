from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_INTERPRETATION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SIGNAL_INTERPRETATION_20260412_v0.json"
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


def _classify(
    *,
    execution_terminal_outcome: str,
    ruling_status: str,
    ruling_terminal_outcome: str,
    signal_strength: float,
    signal_threshold: float,
    noise_floor: float,
    probe_ready_signal_margin: float,
    externally_comparable_signal_margin: float,
    insufficient_hold_signal_margin: float,
    noise_floor_max: float,
) -> str:
    if execution_terminal_outcome != "BRIDGE_SEAM_SIGNAL_PRODUCED":
        return "BRIDGE_SIGNAL_INTERNAL_ONLY"
    if ruling_status != "TERMINAL_OUTCOME_CONFIRMED" or ruling_terminal_outcome != "BRIDGE_SEAM_SIGNAL_PRODUCED":
        return "BRIDGE_SIGNAL_INTERNAL_ONLY"

    margin = signal_strength - signal_threshold
    if margin >= probe_ready_signal_margin and noise_floor <= noise_floor_max:
        return "BRIDGE_SIGNAL_PROBE_READY"
    if margin >= externally_comparable_signal_margin and noise_floor <= noise_floor_max:
        return "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE"
    if margin <= insufficient_hold_signal_margin or noise_floor > noise_floor_max:
        return "BRIDGE_SIGNAL_INSUFFICIENT_HOLD"
    return "BRIDGE_SIGNAL_INTERNAL_ONLY"


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    policy = dict(declaration.get("adjudication_policy", {}))

    execution_path = REPO_ROOT / str(required_inputs.get("bridge_first_test_execution_report", "")).strip()
    ruling_path = REPO_ROOT / str(required_inputs.get("bridge_first_test_ruling_report", "")).strip()
    packet_path = REPO_ROOT / str(required_inputs.get("bridge_first_test_packet_report", "")).strip()

    execution = _read_json(execution_path)
    ruling = _read_json(ruling_path)
    packet = _read_json(packet_path)

    execution_summary = dict(execution.get("summary", {}))
    ruling_summary = dict(ruling.get("summary", {}))
    packet_summary = dict(packet.get("summary", {}))
    packet_criteria = dict(packet.get("criteria", {}))

    execution_terminal_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    ruling_status = str(ruling_summary.get("ruling_status", "")).strip()
    ruling_terminal_outcome = str(ruling_summary.get("terminal_outcome", "")).strip()
    packet_terminal_outcome = str(packet_summary.get("terminal_outcome", "")).strip()

    signal_strength = float(execution_summary.get("observed_signal_strength", 0.0))
    signal_threshold = float(execution_summary.get("signal_threshold", 0.0))
    # Noise floor is intentionally bounded as a simple first adjudication signal quality proxy.
    noise_floor = abs(signal_threshold) * 0.2

    probe_ready_signal_margin = float(policy.get("probe_ready_signal_margin", 0.1))
    externally_comparable_signal_margin = float(policy.get("externally_comparable_signal_margin", 0.0))
    insufficient_hold_signal_margin = float(policy.get("insufficient_hold_signal_margin", -0.02))
    noise_floor_max = float(policy.get("noise_floor_max", 0.03))

    interpretation_outcome = _classify(
        execution_terminal_outcome=execution_terminal_outcome,
        ruling_status=ruling_status,
        ruling_terminal_outcome=ruling_terminal_outcome,
        signal_strength=signal_strength,
        signal_threshold=signal_threshold,
        noise_floor=noise_floor,
        probe_ready_signal_margin=probe_ready_signal_margin,
        externally_comparable_signal_margin=externally_comparable_signal_margin,
        insufficient_hold_signal_margin=insufficient_hold_signal_margin,
        noise_floor_max=noise_floor_max,
    )

    allowed_outcomes = [str(x) for x in policy.get("allowed_outcomes", [])]
    if interpretation_outcome not in allowed_outcomes:
        interpretation_outcome = str(policy.get("default_outcome", "BRIDGE_SIGNAL_INTERNAL_ONLY")).strip()

    if interpretation_outcome == "BRIDGE_SIGNAL_PROBE_READY":
        next_action = "AUTHORIZE_ONE_BOUNDED_EXTERNAL_PROBE_PACKET"
    elif interpretation_outcome == "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE":
        next_action = "PREPARE_EXTERNAL_COMPARATOR_BINDING_PACKET"
    elif interpretation_outcome == "BRIDGE_SIGNAL_INSUFFICIENT_HOLD":
        next_action = "HOLD_AND_IMPROVE_SIGNAL_QUALITY_WITHOUT_SCOPE_EXPANSION"
    else:
        next_action = "MAINTAIN_INTERNAL_ONLY_CLASSIFICATION"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "first_packet_executable": packet_terminal_outcome == "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE",
            "execution_signal_produced": execution_terminal_outcome == "BRIDGE_SEAM_SIGNAL_PRODUCED",
            "ruling_confirms_signal": ruling_status == "TERMINAL_OUTCOME_CONFIRMED"
            and ruling_terminal_outcome == "BRIDGE_SEAM_SIGNAL_PRODUCED",
            "bridge_observable_ready": bool(packet_criteria.get("bridge_observable_ready", False)),
            "single_terminal_outcome_rule_declared": str(policy.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_INTERPRETATION_OUTCOME",
            "no_loop_rule_declared": str(policy.get("no_loop_rule", "")).strip()
            == "ONE_BRIDGE_SIGNAL_INTERPRETATION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": interpretation_outcome in set(allowed_outcomes),
                "single_outcome_materialized": True,
                "bounded_signal_quality_measure_used": True,
            },
            "inputs": {
                "execution_terminal_outcome": execution_terminal_outcome,
                "ruling_status": ruling_status,
                "ruling_terminal_outcome": ruling_terminal_outcome,
                "packet_terminal_outcome": packet_terminal_outcome,
                "signal_strength": signal_strength,
                "signal_threshold": signal_threshold,
                "signal_margin": signal_strength - signal_threshold,
                "noise_floor": noise_floor,
                "noise_floor_max": noise_floor_max,
                "allowed_outcomes": allowed_outcomes,
            },
            "summary": {
                "all_criteria_satisfied": interpretation_outcome in {
                    "BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE",
                    "BRIDGE_SIGNAL_PROBE_READY",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "interpretation_outcome": interpretation_outcome,
            "signal_strength": signal_strength,
            "signal_threshold": signal_threshold,
            "signal_margin": signal_strength - signal_threshold,
            "noise_floor": noise_floor,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_first_test_execution_report": _ptr(execution_path),
            "bridge_first_test_ruling_report": _ptr(ruling_path),
            "bridge_first_test_packet_report": _ptr(packet_path),
        },
        "non_claim_boundary": "Repository-local bridge signal interpretation/adjudication report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 bridge signal interpretation/adjudication report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json",
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
        "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_report: "
        f"interpretation_outcome={payload['summary']['interpretation_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())