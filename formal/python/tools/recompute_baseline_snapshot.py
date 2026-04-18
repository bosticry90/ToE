from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from formal.python.tools import recompute_surface_helpers as helpers


REPO_ROOT = helpers.REPO_ROOT
SCHEMA_ID = "RECOMPUTE_BASELINE_SNAPSHOT_REPORT_20260418_v0"
DEFAULT_OUT_PATH = helpers.BASELINE_REPORT_PATH


def _surface_baseline(surface_id: str) -> dict[str, Any]:
    document = helpers.ensure_surface_document(surface_id)
    latest = helpers.latest_trigger(document)
    trigger_count = len(document.get("triggers", []))
    trigger_id = latest.get("trigger_id") if latest else None

    if surface_id == "qm_seam_coherence":
        baseline_values = {
            "coherence_metric": helpers.quantize(0.62 + 0.01 * trigger_count),
            "state_transition_velocity": helpers.quantize(0.14 + 0.005 * trigger_count),
            "ledger_flux_reference": helpers.quantize(0.31 + 0.012 * trigger_count),
        }
    elif surface_id == "ledger_artifact_transport":
        baseline_values = {
            "artifact_flux": helpers.quantize(0.37 + 0.015 * trigger_count),
            "transport_state": helpers.quantize(0.29 + 0.011 * trigger_count),
            "binding_tightness": helpers.quantize(0.41 + 0.01 * trigger_count),
        }
    else:
        baseline_values = {
            "propagation_latency": helpers.quantize(0.48 + 0.009 * trigger_count),
            "transport_coupling": helpers.quantize(0.35 + 0.007 * trigger_count),
            "downstream_consequence_magnitude": helpers.quantize(0.22 + 0.008 * trigger_count),
        }

    return {
        "surface_id": surface_id,
        "surface_path": str(helpers.surface_path(surface_id).relative_to(REPO_ROOT)).replace("\\", "/"),
        "latest_trigger_id": trigger_id,
        "trigger_count": trigger_count,
        "baseline_values": baseline_values,
    }


def build_report(*, captured_at_utc: str | None) -> dict[str, Any]:
    authority_report = helpers.read_json(helpers.AUTHORITY_PROMOTION_REPORT_PATH)
    packet_chain_report = helpers.read_json(helpers.PACKET_CHAIN_REPORT_PATH)

    surfaces = {surface_id: _surface_baseline(surface_id) for surface_id in helpers.SURFACE_SPECS}

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": helpers.utc_now(captured_at_utc),
        "non_claim_boundary": "Repository-local recompute baseline snapshot only; no scientific adequacy claim.",
        "summary": {
            "baseline_surfaces": len(surfaces),
            "authority_registration_completed": authority_report.get("summary", {}).get("registration_completed"),
            "packet_chain_outcome": packet_chain_report.get("summary", {}).get("terminal_outcome"),
        },
        "source_bundle": {
            "authority_promotion_registration_report": str(helpers.AUTHORITY_PROMOTION_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "post_plan_bounded_coupling_refinement_packet_chain_report": str(helpers.PACKET_CHAIN_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        },
        "surface_baselines": surfaces,
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the recompute baseline snapshot report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(captured_at_utc=ns.captured_at_utc)
    helpers.write_json(out, payload)
    print(
        "recompute_baseline_snapshot: "
        f"surfaces={payload['summary']['baseline_surfaces']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())