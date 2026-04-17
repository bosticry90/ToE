from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_REPORT_20260416_v0"

DEFAULT_REFINEMENT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_stat_rl10_computational_analysis_packet_01_refinement_01_v0.json"
)
DEFAULT_BASELINE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_20260416_v0.json"
)
DEFAULT_SIGNAL_INTERPRETATION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_signal_interpretation_20260412_v0.json"
)
DEFAULT_PROBE_RULING_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_rl10_discrete_transition_bridge_probe_ruling_20260412_v0.json"
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
    refinement_path: Path,
    baseline_report_path: Path,
    signal_interpretation_report_path: Path,
    probe_ruling_report_path: Path,
    captured_at_utc: str | None,
) -> dict[str, Any]:
    refinement = _read_json(refinement_path)
    baseline_report = _read_json(baseline_report_path)
    signal_interpretation = _read_json(signal_interpretation_report_path)
    probe_ruling = _read_json(probe_ruling_report_path)

    payload = dict(refinement.get("payload", {}))
    baseline_findings = dict(baseline_report.get("classificatory_findings", {}))
    baseline_criteria = dict(baseline_report.get("criteria", {}))
    signal_inputs = dict(dict(signal_interpretation.get("objective_quality", {})).get("inputs", {}))
    probe_summary = dict(probe_ruling.get("summary", {}))

    signal_margin = float(signal_inputs.get("signal_margin", 0.0))
    refined_value = float(payload.get("refined_value", 0.0))
    stable = (
        str(baseline_findings.get("stability_classification", "")).strip() == "STABLE_v0"
        and bool(baseline_criteria.get("packet_decision_forced_inconclusive", False))
    )
    comparator_sensitive = signal_margin >= refined_value
    discriminator_bearing = str(probe_summary.get("terminal_outcome", "")).strip() == "PROBE_SIGNAL_CONFIRMED"

    stability_classification = "STABLE_v0" if stable else "UNSTABLE_v0"
    comparator_classification = "COMPARATOR_SENSITIVE_v0" if comparator_sensitive else "COMPARATOR_INSENSITIVE_v0"
    discriminator_classification = "DISCRIMINATIVE_v0" if discriminator_bearing else "NONDISCRIMINATIVE_v0"

    if stable and comparator_sensitive and discriminator_bearing:
        subordinate_disposition = "RETAIN_v0"
    elif not stable:
        subordinate_disposition = "PRUNE_v0"
    else:
        subordinate_disposition = "INCONCLUSIVE_v0"

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "QM_STAT_RL10_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "same_auxiliary_authorization_class": str(payload.get("authorization_class", "")).strip() == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
            "same_packet_level_inconclusive_ceiling": str(payload.get("decision", "")).strip() == "INCONCLUSIVE_v0",
            "one_refinement_only": int(payload.get("refinement_sequence", 0)) == 1 and int(payload.get("max_refinements_authorized", 0)) == 1,
            "packet02_authorized": bool(payload.get("packet02_authorized", False)),
            "restart_implication": bool(payload.get("restart_implication", False)),
            "blocker_movement_claim": bool(payload.get("blocker_movement_claim", False)),
            "stable_under_refined_margin": stable,
            "comparator_sensitive_under_refined_margin": comparator_sensitive,
            "discriminator_bearing_under_refined_margin": discriminator_bearing,
        },
        "summary": {
            "packet_decision": "INCONCLUSIVE_v0",
            "stability_classification": stability_classification,
            "comparator_classification": comparator_classification,
            "discriminator_classification": discriminator_classification,
            "subordinate_disposition": subordinate_disposition,
            "variation_id": str(payload.get("variation_id", "")).strip(),
            "variation_axis": str(payload.get("variation_axis", "")).strip(),
            "baseline_value": float(payload.get("baseline_value", 0.0)),
            "refined_value": refined_value,
            "observed_signal_margin": signal_margin,
            "next_action": "CLOSE_PACKET01_FAMILY_WITH_ONE_BOUNDED_REFINEMENT_DECISION",
        },
        "source_bundle": {
            "refinement_artifact": _ptr(refinement_path),
            "baseline_report": _ptr(baseline_report_path),
            "signal_interpretation_report": _ptr(signal_interpretation_report_path),
            "probe_ruling_report": _ptr(probe_ruling_report_path),
        },
        "non_claim_boundary": "Repository-local Packet-01 refinement report only; no Packet-02 authorization, restart implication, blocker movement, lane reopen, or external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT RL10 computational-analysis Packet-01 refinement 01 report.")
    parser.add_argument("--refinement", type=Path, default=DEFAULT_REFINEMENT_PATH)
    parser.add_argument("--baseline-report", type=Path, default=DEFAULT_BASELINE_REPORT_PATH)
    parser.add_argument("--signal-interpretation-report", type=Path, default=DEFAULT_SIGNAL_INTERPRETATION_REPORT_PATH)
    parser.add_argument("--probe-ruling-report", type=Path, default=DEFAULT_PROBE_RULING_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_rl10_computational_analysis_packet_01_refinement_01_20260416_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    refinement_path = ns.refinement if ns.refinement.is_absolute() else (REPO_ROOT / ns.refinement)
    baseline_report_path = ns.baseline_report if ns.baseline_report.is_absolute() else (REPO_ROOT / ns.baseline_report)
    signal_interpretation_report_path = ns.signal_interpretation_report if ns.signal_interpretation_report.is_absolute() else (REPO_ROOT / ns.signal_interpretation_report)
    probe_ruling_report_path = ns.probe_ruling_report if ns.probe_ruling_report.is_absolute() else (REPO_ROOT / ns.probe_ruling_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(
        refinement_path=refinement_path,
        baseline_report_path=baseline_report_path,
        signal_interpretation_report_path=signal_interpretation_report_path,
        probe_ruling_report_path=probe_ruling_report_path,
        captured_at_utc=ns.captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "qm_stat_rl10_computational_analysis_packet_01_refinement_01_report: "
        f"packet_decision={payload['summary']['packet_decision']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())