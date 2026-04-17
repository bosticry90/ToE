from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REPORT_20260416_v0"

DEFAULT_PACKET_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_v0.json"
)
DEFAULT_FIRST_TEST_PACKET_REPORT = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_discrete_transition_bridge_first_test_packet_20260412_v0.json"
)
DEFAULT_SIGNAL_INTERPRETATION_REPORT = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json"
)
DEFAULT_COMPARATOR_BINDING_RULING_REPORT = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_discrete_transition_bridge_external_comparator_binding_ruling_20260412_v0.json"
)
DEFAULT_PROBE_RULING_REPORT = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json"
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


def build_report(
    *,
    packet_path: Path,
    first_test_packet_report_path: Path,
    signal_interpretation_report_path: Path,
    comparator_binding_ruling_report_path: Path,
    probe_ruling_report_path: Path,
    captured_at_utc: str | None,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    first_test_packet = _read_json(first_test_packet_report_path)
    signal_interpretation = _read_json(signal_interpretation_report_path)
    comparator_binding = _read_json(comparator_binding_ruling_report_path)
    probe_ruling = _read_json(probe_ruling_report_path)

    packet_payload = dict(packet.get("payload", {}))
    first_test_summary = dict(first_test_packet.get("summary", {}))
    first_test_criteria = dict(first_test_packet.get("criteria", {}))
    signal_summary = dict(signal_interpretation.get("summary", {}))
    comparator_summary = dict(comparator_binding.get("summary", {}))
    probe_summary = dict(probe_ruling.get("summary", {}))

    stable = (
        str(first_test_summary.get("terminal_outcome", "")).strip() == "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE"
        and bool(first_test_criteria.get("transition_structure_coherent", False))
        and bool(first_test_criteria.get("bridge_observable_ready", False))
        and bool(first_test_criteria.get("governance_boundary_preserved", False))
    )
    comparator_sensitive = (
        str(signal_summary.get("interpretation_outcome", "")).strip()
        in {"BRIDGE_SIGNAL_EXTERNALLY_COMPARABLE_CANDIDATE", "BRIDGE_SIGNAL_PROBE_READY"}
        or str(comparator_summary.get("terminal_outcome", "")).strip() == "EXTERNAL_COMPARATOR_BINDING_CONFIRMED"
    )
    discriminator_bearing = str(probe_summary.get("terminal_outcome", "")).strip() == "PROBE_SIGNAL_CONFIRMED"
    falsified = any(
        outcome in {
            "BRIDGE_SEAM_PATH_FALSIFIED",
            "BRIDGE_SIGNAL_PATH_FALSIFIED",
            "PROBE_PATH_FALSIFIED",
        }
        for outcome in (
            str(first_test_summary.get("terminal_outcome", "")).strip(),
            str(comparator_summary.get("terminal_outcome", "")).strip(),
            str(probe_summary.get("terminal_outcome", "")).strip(),
        )
    )

    stability_classification = "STABLE_v0" if stable else "UNSTABLE_v0"
    comparator_classification = "COMPARATOR_SENSITIVE_v0" if comparator_sensitive else "COMPARATOR_INSENSITIVE_v0"
    discriminator_classification = "DISCRIMINATIVE_v0" if discriminator_bearing else "NONDISCRIMINATIVE_v0"

    if falsified or not stable:
        subordinate_disposition = "PRUNE_v0"
    elif comparator_sensitive or discriminator_bearing:
        subordinate_disposition = "RETAIN_v0"
    else:
        subordinate_disposition = "INCONCLUSIVE_v0"

    packet_decision = "INCONCLUSIVE_v0"
    next_action = "RETAIN_REFINE_OR_RETIRE_PACKET_01_BEFORE_ANY_PACKET_02"

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_status_bound_nonclaim": str(packet_payload.get("status", "")).strip() == "RUN_BOUNDED_v0_NONCLAIM",
            "packet_decision_forced_inconclusive": str(packet_payload.get("decision", "")).strip() == "INCONCLUSIVE_v0",
            "bridge_structure_currently_executable": stable,
            "comparator_signal_present": comparator_sensitive,
            "discriminator_signal_present": discriminator_bearing,
            "restart_semantics_preserved": True,
        },
        "classificatory_findings": {
            "stability_classification": stability_classification,
            "comparator_classification": comparator_classification,
            "discriminator_classification": discriminator_classification,
            "subordinate_disposition": subordinate_disposition,
        },
        "summary": {
            "packet_decision": packet_decision,
            "stability_classification": stability_classification,
            "comparator_classification": comparator_classification,
            "discriminator_classification": discriminator_classification,
            "subordinate_disposition": subordinate_disposition,
            "next_action": next_action,
        },
        "source_bundle": {
            "packet_artifact": _ptr(packet_path),
            "first_test_packet_report": _ptr(first_test_packet_report_path),
            "signal_interpretation_report": _ptr(signal_interpretation_report_path),
            "external_comparator_binding_ruling_report": _ptr(comparator_binding_ruling_report_path),
            "probe_ruling_report": _ptr(probe_ruling_report_path),
        },
        "non_claim_boundary": "Repository-local auxiliary computational-analysis packet report only; no lane reopen, restart authorization, blocker movement, or external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QM-STAT RL10 computational-analysis Packet-01 report."
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--first-test-packet-report", type=Path, default=DEFAULT_FIRST_TEST_PACKET_REPORT)
    parser.add_argument("--signal-interpretation-report", type=Path, default=DEFAULT_SIGNAL_INTERPRETATION_REPORT)
    parser.add_argument("--comparator-binding-ruling-report", type=Path, default=DEFAULT_COMPARATOR_BINDING_RULING_REPORT)
    parser.add_argument("--probe-ruling-report", type=Path, default=DEFAULT_PROBE_RULING_REPORT)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_computational_analysis_packet_01_20260416_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    first_test_packet_report_path = (
        ns.first_test_packet_report
        if ns.first_test_packet_report.is_absolute()
        else (REPO_ROOT / ns.first_test_packet_report)
    )
    signal_interpretation_report_path = (
        ns.signal_interpretation_report
        if ns.signal_interpretation_report.is_absolute()
        else (REPO_ROOT / ns.signal_interpretation_report)
    )
    comparator_binding_ruling_report_path = (
        ns.comparator_binding_ruling_report
        if ns.comparator_binding_ruling_report.is_absolute()
        else (REPO_ROOT / ns.comparator_binding_ruling_report)
    )
    probe_ruling_report_path = (
        ns.probe_ruling_report
        if ns.probe_ruling_report.is_absolute()
        else (REPO_ROOT / ns.probe_ruling_report)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(
        packet_path=packet_path,
        first_test_packet_report_path=first_test_packet_report_path,
        signal_interpretation_report_path=signal_interpretation_report_path,
        comparator_binding_ruling_report_path=comparator_binding_ruling_report_path,
        probe_ruling_report_path=probe_ruling_report_path,
        captured_at_utc=ns.captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "qm_stat_rl10_computational_analysis_packet_01_report: "
        f"packet_decision={payload['summary']['packet_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())