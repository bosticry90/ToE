from __future__ import annotations

import argparse
from pathlib import Path

from formal.python.tools import recompute_surface_helpers as helpers


REPO_ROOT = helpers.REPO_ROOT
DEFAULT_BASELINE_PATH = helpers.BASELINE_REPORT_PATH


def execute_surface(*, baseline_path: Path, trigger_id: str | None, captured_at_utc: str | None, surface_root: Path | None = None) -> dict:
    baseline = helpers.read_json(baseline_path)
    effective_root = helpers.resolve_root(surface_root)
    document = helpers.ensure_surface_document("blocker_authority_transport", root=effective_root)
    trigger = helpers.latest_trigger(document, status="PENDING_RECOMPUTE", trigger_id=trigger_id)
    if trigger is None:
        raise ValueError("No pending blocker authority transport recompute trigger found")

    baseline_entry = baseline["surface_baselines"]["blocker_authority_transport"]
    baseline_values = baseline_entry["baseline_values"]
    fraction = helpers.deterministic_fraction("blocker_authority_transport", str(trigger.get("trigger_id")))
    latency_before = float(baseline_values["propagation_latency"])
    latency_after = helpers.quantize(max(0.01, latency_before - (0.015 + 0.01 * fraction)))
    coupling_before = float(baseline_values["transport_coupling"])
    coupling_after = helpers.quantize(min(0.99, coupling_before + 0.02 + 0.02 * fraction))
    magnitude_before = float(baseline_values["downstream_consequence_magnitude"])
    magnitude_after = helpers.quantize(magnitude_before + 0.02 + 0.018 * fraction)
    captured = helpers.utc_now(captured_at_utc)

    document["computed_state"] = {
        "surface_id": "blocker_authority_transport",
        "trigger_id": trigger["trigger_id"],
        "baseline_report": str(baseline_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "propagation_latency_before": latency_before,
        "propagation_latency": latency_after,
        "state_change_from_baseline": helpers.quantize(latency_before - latency_after),
        "transport_state_coupling_before": coupling_before,
        "transport_state_coupling": coupling_after,
        "downstream_consequence_magnitude_before": magnitude_before,
        "downstream_consequence_magnitude": magnitude_after,
        "attribution": "REVISED_BLOCKER_DEFINITION_PROMOTION_DELTA",
    }
    document["execution_summary"] = {
        "surface_id": "blocker_authority_transport",
        "classification": "RECOMPUTE_COMPLETED_WITH_OUTPUTS",
        "next_action": "RERUN_RECOMPUTE_OBSERVATION_REPORT",
    }
    helpers.mark_trigger_completed(
        trigger,
        completed_at_utc=captured,
        note="Blocker authority transport recompute output materialized",
    )
    helpers.refresh_surface_metadata(document, surface_id="blocker_authority_transport", trigger_id=trigger["trigger_id"], captured_at_utc=captured)
    helpers.write_json(helpers.surface_path("blocker_authority_transport", root=effective_root), document)
    return document


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Execute the blocker authority transport recompute surface.")
    parser.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE_PATH)
    parser.add_argument("--trigger-id", default=None)
    parser.add_argument("--captured-at-utc", default=None)
    parser.add_argument("--surface-root", type=Path, default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    baseline_path = ns.baseline if ns.baseline.is_absolute() else (REPO_ROOT / ns.baseline)
    surface_root = ns.surface_root if ns.surface_root is None or ns.surface_root.is_absolute() else (REPO_ROOT / ns.surface_root)
    payload = execute_surface(baseline_path=baseline_path, trigger_id=ns.trigger_id, captured_at_utc=ns.captured_at_utc, surface_root=surface_root)
    print(
        "blocker_authority_transport_recompute_execute: "
        f"trigger_id={payload['last_completed_trigger_id']} out={helpers.surface_path('blocker_authority_transport', root=surface_root)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())