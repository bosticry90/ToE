from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REPORT_20260417_v0"

DEFAULT_PACKET_PATH = REPO_ROOT / "formal" / "output" / "toe_master_action_computational_analysis_packet_01_v0.json"


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


def _classify_packet(*, spectral_radius: float, residual_norm: float, regime_span: float, ordering_preserved: bool) -> str:
    if spectral_radius >= 1.0 or residual_norm >= 0.10 or not ordering_preserved:
        return "RETIRE_CANDIDATE_v0"
    if regime_span >= 0.010:
        return "REFINE_CANDIDATE_v0"
    if residual_norm <= 0.06:
        return "RETAIN_CANDIDATE_v0"
    return "INCONCLUSIVE_BOUNDARY_v0"


def build_report(*, packet_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    packet = _read_json(packet_path)
    payload = dict(packet.get("payload", {}))

    operator = np.array(payload.get("operator_matrix", []), dtype=float)
    state = np.array(payload.get("state_vector", []), dtype=float)
    residual_target = np.array(payload.get("residual_target", []), dtype=float)
    perturbation_schedule = [float(value) for value in payload.get("perturbation_schedule", [])]

    if operator.shape != (3, 3):
        raise ValueError("Packet-01 operator matrix must be 3x3.")
    if state.shape != (3,):
        raise ValueError("Packet-01 state vector must have length 3.")
    if residual_target.shape != (3,):
        raise ValueError("Packet-01 residual target must have length 3.")
    if not perturbation_schedule:
        raise ValueError("Packet-01 perturbation schedule must be non-empty.")

    eigenvalues = np.linalg.eigvals(operator)
    spectral_radius = float(np.max(np.abs(eigenvalues)))
    operator_response = operator @ state
    residual = operator_response - residual_target
    residual_norm = float(np.linalg.norm(residual))
    residual_mean_abs = float(np.mean(np.abs(residual)))

    baseline_order = np.argsort(-operator_response)
    regime_rows: list[dict[str, Any]] = []
    regime_residual_norms: list[float] = []
    ordering_preserved = True
    for delta in perturbation_schedule:
        perturbed_operator = operator + np.diag([delta, -0.5 * delta, 0.25 * delta])
        perturbed_response = perturbed_operator @ state
        perturbed_residual = perturbed_response - residual_target
        perturbed_norm = float(np.linalg.norm(perturbed_residual))
        regime_residual_norms.append(perturbed_norm)
        order_matches = bool(np.array_equal(np.argsort(-perturbed_response), baseline_order))
        ordering_preserved = ordering_preserved and order_matches
        regime_rows.append(
            {
                "perturbation": delta,
                "response_vector": [round(float(value), 6) for value in perturbed_response],
                "residual_norm": round(perturbed_norm, 6),
                "ordering_preserved": order_matches,
            }
        )

    regime_span = float(max(regime_residual_norms) - min(regime_residual_norms))
    operator_stability_pass = spectral_radius < 1.0
    residual_consistency_pass = residual_norm < 0.10 and residual_mean_abs < 0.05
    regime_limit_sensitivity_pass = ordering_preserved and regime_span < 0.08

    subordinate_disposition = _classify_packet(
        spectral_radius=spectral_radius,
        residual_norm=residual_norm,
        regime_span=regime_span,
        ordering_preserved=ordering_preserved,
    )

    return {
        "schema_id": SCHEMA_ID,
        "report_id": "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_REPORT_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_status_bound_nonclaim": str(payload.get("status", "")).strip() == "RUN_BOUNDED_v0_NONCLAIM",
            "numpy_reference_stack_only": str(payload.get("implementation_stack", "")).strip() == "NUMPY_FIRST_REFERENCE_IMPLEMENTATION_ONLY",
            "operator_stability_pass": operator_stability_pass,
            "residual_consistency_pass": residual_consistency_pass,
            "regime_limit_sensitivity_pass": regime_limit_sensitivity_pass,
            "ordering_preserved_across_regime_scan": ordering_preserved,
            "refinement_ceiling_preserved": True,
        },
        "numeric_summary": {
            "spectral_radius": round(spectral_radius, 6),
            "residual_norm": round(residual_norm, 6),
            "residual_mean_abs": round(residual_mean_abs, 6),
            "regime_limit_residual_span": round(regime_span, 6),
        },
        "classificatory_findings": {
            "operator_stability_observable": {
                "observable_id": "operator_stability_observable_v0",
                "pass": operator_stability_pass,
                "spectral_radius": round(spectral_radius, 6),
            },
            "residual_consistency_observable": {
                "observable_id": "residual_consistency_observable_v0",
                "pass": residual_consistency_pass,
                "residual_norm": round(residual_norm, 6),
                "residual_mean_abs": round(residual_mean_abs, 6),
            },
            "regime_limit_sensitivity_observable": {
                "observable_id": "regime_limit_sensitivity_observable_v0",
                "pass": regime_limit_sensitivity_pass,
                "regime_limit_residual_span": round(regime_span, 6),
                "scan_rows": regime_rows,
            },
            "subordinate_disposition": subordinate_disposition,
        },
        "summary": {
            "packet_decision": "INCONCLUSIVE_v0",
            "subordinate_disposition": subordinate_disposition,
            "next_action": "ROUTE_TO_BOUNDED_PACKET01_DECISION_SURFACE_ONLY",
        },
        "source_bundle": {
            "packet_artifact": _ptr(packet_path),
            "packet_contract": "formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md",
            "candidate_master_action": "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md",
        },
        "non_claim_boundary": "Repository-local master-action Packet-01 computational-analysis report only; no theorem promotion, canonical action promotion, blocker movement, lane reopen, Packet-02 authorization, or external-truth claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the ToE master-action computational-analysis Packet-01 report.")
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_20260417_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(packet_path=packet_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "toe_master_action_computational_analysis_packet_01_report: "
        f"subordinate_disposition={payload['summary']['subordinate_disposition']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())