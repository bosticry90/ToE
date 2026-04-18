from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import toe_master_action_computational_analysis_packet_01_report as baseline_tool


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_REPORT_20260417_v0"

DEFAULT_REFINEMENT_PATH = REPO_ROOT / "formal" / "output" / "toe_master_action_computational_analysis_packet_01_refinement_01_v0.json"
DEFAULT_BASELINE_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_20260417_v0.json"


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


def build_report(*, refinement_path: Path, baseline_report_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    refinement = _read_json(refinement_path)
    baseline_report = _read_json(baseline_report_path)
    refined_report = baseline_tool.build_report(packet_path=refinement_path, captured_at_utc=captured_at_utc)

    payload = dict(refinement.get("payload", {}))
    baseline_numeric = dict(baseline_report.get("numeric_summary", {}))
    baseline_findings = dict(baseline_report.get("classificatory_findings", {}))
    refined_numeric = dict(refined_report.get("numeric_summary", {}))
    refined_criteria = dict(refined_report.get("criteria", {}))

    baseline_span = float(baseline_numeric.get("regime_limit_residual_span", 9.9))
    refined_span = float(refined_numeric.get("regime_limit_residual_span", 9.9))
    baseline_residual = float(baseline_numeric.get("residual_norm", 9.9))
    refined_residual = float(refined_numeric.get("residual_norm", 9.9))
    baseline_spectral = float(baseline_numeric.get("spectral_radius", 9.9))
    refined_spectral = float(refined_numeric.get("spectral_radius", 9.9))

    boundary_preserved = (
        str(payload.get("authorization_class", "")).strip() == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
        and str(payload.get("decision", "")).strip() == "INCONCLUSIVE_v0"
        and int(payload.get("refinement_sequence", 0)) == 1
        and int(payload.get("max_refinements_authorized", 0)) == 1
        and not bool(payload.get("packet02_authorized", False))
        and not bool(payload.get("gpu_backend_authorized", False))
        and not bool(payload.get("lane_reopen_implication", False))
        and not bool(payload.get("blocker_movement_claim", False))
    )
    regime_span_tightened = refined_span < baseline_span
    residual_nondegrading = refined_residual <= baseline_residual + 1e-9
    spectral_radius_nonworsening = refined_spectral <= baseline_spectral + 1e-9
    baseline_subordinate = str(baseline_findings.get("subordinate_disposition", "")).strip()

    if boundary_preserved and regime_span_tightened and residual_nondegrading and spectral_radius_nonworsening:
        refinement_recommendation = "RETAIN_REFINEMENT_v0"
    elif boundary_preserved and refined_criteria.get("operator_stability_pass", False) and refined_criteria.get("residual_consistency_pass", False):
        refinement_recommendation = "RETAIN_BASELINE_v0"
    elif not boundary_preserved:
        refinement_recommendation = "RETIRE_REFINEMENT_v0"
    else:
        refinement_recommendation = "STOP_PACKET01_FAMILY_v0"

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REFINEMENT_01_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "same_auxiliary_authorization_class": str(payload.get("authorization_class", "")).strip() == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
            "same_packet_level_inconclusive_ceiling": str(payload.get("decision", "")).strip() == "INCONCLUSIVE_v0",
            "one_refinement_only": int(payload.get("refinement_sequence", 0)) == 1 and int(payload.get("max_refinements_authorized", 0)) == 1,
            "packet02_authorized": bool(payload.get("packet02_authorized", False)),
            "gpu_backend_authorized": bool(payload.get("gpu_backend_authorized", False)),
            "lane_reopen_implication": bool(payload.get("lane_reopen_implication", False)),
            "blocker_movement_claim": bool(payload.get("blocker_movement_claim", False)),
            "operator_stability_preserved": bool(refined_criteria.get("operator_stability_pass", False)),
            "residual_consistency_preserved": bool(refined_criteria.get("residual_consistency_pass", False)),
            "regime_span_tightened": regime_span_tightened,
            "residual_nondegrading": residual_nondegrading,
            "spectral_radius_nonworsening": spectral_radius_nonworsening,
        },
        "summary": {
            "packet_decision": "INCONCLUSIVE_v0",
            "baseline_subordinate_disposition": baseline_subordinate,
            "refinement_recommendation": refinement_recommendation,
            "variation_id": str(payload.get("variation_id", "")).strip(),
            "variation_axis": str(payload.get("variation_axis", "")).strip(),
            "baseline_value": float(payload.get("baseline_value", 0.0)),
            "refined_value": float(payload.get("refined_value", 0.0)),
            "baseline_regime_limit_residual_span": round(baseline_span, 6),
            "refined_regime_limit_residual_span": round(refined_span, 6),
            "next_action": "CLOSE_PACKET01_FAMILY_WITH_SINGLE_REFINEMENT_CLOSEOUT",
        },
        "numeric_summary": {
            "baseline_spectral_radius": round(baseline_spectral, 6),
            "refined_spectral_radius": round(refined_spectral, 6),
            "baseline_residual_norm": round(baseline_residual, 6),
            "refined_residual_norm": round(refined_residual, 6),
            "baseline_regime_limit_residual_span": round(baseline_span, 6),
            "refined_regime_limit_residual_span": round(refined_span, 6),
        },
        "source_bundle": {
            "refinement_artifact": _ptr(refinement_path),
            "baseline_report": _ptr(baseline_report_path),
            "refined_execution_report_logic": "formal/python/tools/toe_master_action_computational_analysis_packet_01_report.py",
        },
        "non_claim_boundary": "Repository-local master-action Packet-01 refinement report only; no Packet-02 authorization, no GPU migration, no lane reopen, no blocker movement, and no external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the ToE master-action Packet-01 refinement 01 report.")
    parser.add_argument("--refinement", type=Path, default=DEFAULT_REFINEMENT_PATH)
    parser.add_argument("--baseline-report", type=Path, default=DEFAULT_BASELINE_REPORT_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_refinement_01_20260417_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    refinement_path = ns.refinement if ns.refinement.is_absolute() else (REPO_ROOT / ns.refinement)
    baseline_report_path = ns.baseline_report if ns.baseline_report.is_absolute() else (REPO_ROOT / ns.baseline_report)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(refinement_path=refinement_path, baseline_report_path=baseline_report_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "toe_master_action_computational_analysis_packet_01_refinement_01_report: "
        f"recommendation={payload['summary']['refinement_recommendation']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())