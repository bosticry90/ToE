from __future__ import annotations

import argparse
from pathlib import Path

from formal.python.tools import recompute_surface_helpers as helpers


REPO_ROOT = helpers.REPO_ROOT
DEFAULT_BASELINE_PATH = helpers.BASELINE_REPORT_PATH


def execute_surface(*, baseline_path: Path, trigger_id: str | None, captured_at_utc: str | None, surface_root: Path | None = None) -> dict:
    baseline = helpers.read_json(baseline_path)
    effective_root = helpers.resolve_root(surface_root)
    document = helpers.ensure_surface_document("ledger_artifact_transport", root=effective_root)
    trigger = helpers.latest_trigger(document, status="PENDING_RECOMPUTE", trigger_id=trigger_id)
    if trigger is None:
        raise ValueError("No pending ledger artifact transport recompute trigger found")

    baseline_entry = baseline["surface_baselines"]["ledger_artifact_transport"]
    baseline_values = baseline_entry["baseline_values"]
    fraction = helpers.deterministic_fraction("ledger_artifact_transport", str(trigger.get("trigger_id")))
    flux_before = float(baseline_values["artifact_flux"])
    flux_after = helpers.quantize(flux_before + 0.025 + 0.025 * fraction)
    transport_state_before = float(baseline_values["transport_state"])
    transport_state_after = helpers.quantize(transport_state_before + 0.015 + 0.02 * fraction)
    binding_before = float(baseline_values["binding_tightness"])
    binding_after = helpers.quantize(min(0.99, binding_before + 0.02 + 0.015 * fraction))
    captured = helpers.utc_now(captured_at_utc)

    document["computed_state"] = {
        "surface_id": "ledger_artifact_transport",
        "trigger_id": trigger["trigger_id"],
        "baseline_report": str(baseline_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "artifact_flux_before": flux_before,
        "artifact_flux_magnitude": flux_after,
        "state_change_from_baseline": helpers.quantize(flux_after - flux_before),
        "transport_state_before": transport_state_before,
        "transport_state": transport_state_after,
        "authority_to_ledger_binding_tightness_before": binding_before,
        "authority_to_ledger_binding_tightness": binding_after,
        "attribution": "REVISED_BLOCKER_DEFINITION_PROMOTION_DELTA",
    }
    document["execution_summary"] = {
        "surface_id": "ledger_artifact_transport",
        "classification": "RECOMPUTE_COMPLETED_WITH_OUTPUTS",
        "next_action": "RERUN_RECOMPUTE_OBSERVATION_REPORT",
    }
    helpers.mark_trigger_completed(
        trigger,
        completed_at_utc=captured,
        note="Ledger artifact transport recompute output materialized",
    )
    helpers.refresh_surface_metadata(document, surface_id="ledger_artifact_transport", trigger_id=trigger["trigger_id"], captured_at_utc=captured)
    helpers.write_json(helpers.surface_path("ledger_artifact_transport", root=effective_root), document)
    return document


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Execute the ledger artifact transport recompute surface.")
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
        "ledger_artifact_transport_recompute_execute: "
        f"trigger_id={payload['last_completed_trigger_id']} out={helpers.surface_path('ledger_artifact_transport', root=surface_root)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())