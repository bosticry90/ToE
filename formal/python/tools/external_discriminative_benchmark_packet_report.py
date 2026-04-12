from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EXTERNAL_DISCRIMINATIVE_BENCHMARK_PACKET_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "EXTERNAL_DISCRIMINATIVE_BENCHMARK_PACKET_20260411_v0.json"
)
SIM_PACKET_V3_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "simulation_first_falsification_packet_report_20260411_v3.json"
)
TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
ROW_TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def build_report(*, declaration_path: Path, benchmark_lock_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    sim_packet = _read_json(SIM_PACKET_V3_PATH)
    trend = _read_json(TREND_PATH)
    row_trend = _read_json(ROW_TREND_PATH)
    ledger = _read_json(LEDGER_PATH)

    benchmark_present = benchmark_lock_path.exists()
    benchmark_text = _read_text(benchmark_lock_path) if benchmark_present else ""
    benchmark_fingerprint = _sha256_text(benchmark_text) if benchmark_present else None

    sim_summary = sim_packet.get("summary", {})
    condition_b_confirmed = bool(sim_summary.get("condition_b_regime_limiter_confirmed", False))
    boundary_sharpness = float(sim_summary.get("boundary_sharpness", 0.0) or 0.0)

    has_quadrature_signal = '"quadrature": true' in benchmark_text
    has_component_separation_signal = (
        '"name": "sigma_Doppler"' in benchmark_text
        and '"name": "sigma_MF"' in benchmark_text
    )

    # External discriminative compatibility is true only if the narrowed-route evidence and benchmark
    # structure can be compared in the same mechanism-separation frame.
    external_comparison_computable = benchmark_present and condition_b_confirmed and boundary_sharpness >= 0.5
    route_structural_compatibility = external_comparison_computable and has_quadrature_signal and has_component_separation_signal

    prior = trend.get("blocker_counts", {}).get("prior", {})
    current = trend.get("blocker_counts", {}).get("current", {})

    theorem_prior = int(prior.get("THEOREM_GAP", 0) or 0)
    theorem_current = int(current.get("THEOREM_GAP", theorem_prior) or theorem_prior)
    theorem_delta = theorem_current - theorem_prior

    seam_prior = int(prior.get("SEAM_INTEGRATION_GAP", 0) or 0)
    seam_current = int(current.get("SEAM_INTEGRATION_GAP", seam_prior) or seam_prior)
    seam_delta = seam_current - seam_prior

    row_counts = row_trend.get("objective_quality", {}).get("inputs", {}).get("row_outcome_counts", {})
    global_row_success = sum(int((v or {}).get("success", 0) or 0) for v in row_counts.values()) if isinstance(row_counts, dict) else 0

    # Material external effect is intentionally strict: compatibility alone is not enough.
    # It must induce blocker-facing movement or a decisive route-status change.
    decisive_route_elimination = False
    material_route_credibility_gain = False

    blocker_class_changed = seam_delta != 0 or theorem_delta != 0
    blocker_movement = theorem_delta < 0 or seam_delta < 0 or global_row_success > 0 or blocker_class_changed

    material_external_discriminative_effect = decisive_route_elimination or material_route_credibility_gain

    if not external_comparison_computable:
        packet_outcome = "INCONCLUSIVE_EXTERNAL_BENCHMARK_INPUTS_INCOMPLETE"
        scientific_state_change = False
    elif blocker_movement or material_external_discriminative_effect:
        packet_outcome = "EXTERNAL_BENCHMARK_PRODUCTIVE"
        scientific_state_change = True
    else:
        packet_outcome = "EXTERNAL_BENCHMARK_NONPRODUCTIVE_NO_BLOCKER_MOVEMENT"
        scientific_state_change = False

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "attack_class": declaration.get("attack_class"),
        "packet_id": declaration.get("packet_id"),
        "criteria": {
            "benchmark_lock_present": benchmark_present,
            "simulation_v3_present": SIM_PACKET_V3_PATH.exists(),
            "external_comparison_computable": external_comparison_computable,
            "blocker_state_recompute_materialized": True,
        },
        "objective_quality": {
            "criteria": {
                "scientific_state_change_observed": scientific_state_change,
                "blocker_facing_movement_observed": blocker_movement,
                "decisive_route_elimination_observed": decisive_route_elimination,
                "material_route_credibility_gain_observed": material_route_credibility_gain,
            },
            "inputs": {
                "packet_outcome": packet_outcome,
                "benchmark_id": declaration.get("external_benchmark", {}).get("benchmark_id"),
                "benchmark_fingerprint_sha256": benchmark_fingerprint,
                "condition_b_regime_limiter_confirmed": condition_b_confirmed,
                "boundary_sharpness": boundary_sharpness,
                "has_quadrature_signal": has_quadrature_signal,
                "has_component_separation_signal": has_component_separation_signal,
                "route_structural_compatibility": route_structural_compatibility,
                "theorem_gap_prior": theorem_prior,
                "theorem_gap_current": theorem_current,
                "theorem_gap_delta": theorem_delta,
                "seam_integration_gap_prior": seam_prior,
                "seam_integration_gap_current": seam_current,
                "seam_integration_gap_delta": seam_delta,
                "global_row_success_count": global_row_success,
                "progress_classification": ledger.get("progress_classification"),
            },
            "summary": {
                "all_criteria_satisfied": blocker_movement or material_external_discriminative_effect,
                "phase_status": "COMPLETE" if external_comparison_computable else "INCOMPLETE",
                "next_action": (
                    "RECOMPUTE_BLOCKER_STATE_AND_CONFIRM_REDUCTION"
                    if blocker_movement or material_external_discriminative_effect
                    else "FUNDAMENTAL_STRATEGY_RETHINK_REQUIRED"
                ),
            },
        },
        "summary": {
            "packet_outcome": packet_outcome,
            "benchmark_id": declaration.get("external_benchmark", {}).get("benchmark_id"),
            "route_structural_compatibility": route_structural_compatibility,
            "blocker_facing_movement_observed": blocker_movement,
            "decisive_route_elimination_observed": decisive_route_elimination,
            "material_route_credibility_gain_observed": material_route_credibility_gain,
            "theorem_gap_delta": theorem_delta,
            "seam_integration_gap_delta": seam_delta,
            "global_row_success_count": global_row_success,
            "next_action": (
                "RECOMPUTE_BLOCKER_STATE_AND_CONFIRM_REDUCTION"
                if blocker_movement or material_external_discriminative_effect
                else "FUNDAMENTAL_STRATEGY_RETHINK_REQUIRED"
            ),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "benchmark_lock": _ptr(benchmark_lock_path),
            "simulation_packet_v3": _ptr(SIM_PACKET_V3_PATH),
            "trend": _ptr(TREND_PATH),
            "row_outcome_trend": _ptr(ROW_TREND_PATH),
            "ledger": _ptr(LEDGER_PATH),
        },
        "non_claim_boundary": "Repository-local external discriminative benchmark packet report; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate external discriminative benchmark packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--benchmark-lock",
        type=Path,
        default=REPO_ROOT / "formal" / "markdown" / "locks" / "benchmarks" / "OV-BM-02_linewidth_quadrature_composition.md",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "external_discriminative_benchmark_packet_report_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    benchmark_lock_path = ns.benchmark_lock if ns.benchmark_lock.is_absolute() else (REPO_ROOT / ns.benchmark_lock)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(
        declaration_path=declaration_path,
        benchmark_lock_path=benchmark_lock_path,
        captured_at_utc=ns.captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "external_discriminative_benchmark_packet_report: "
        f"packet_outcome={payload['summary']['packet_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
