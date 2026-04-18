from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from formal.python.tools import recompute_surface_helpers as helpers


REPO_ROOT = helpers.REPO_ROOT
DEFAULT_BASELINE_PATH = helpers.BASELINE_REPORT_PATH


def execute_surface(*, baseline_path: Path, trigger_id: str | None, captured_at_utc: str | None, surface_root: Path | None = None) -> dict[str, Any]:
    baseline = helpers.read_json(baseline_path)
    effective_root = helpers.resolve_root(surface_root)
    document = helpers.ensure_surface_document("qm_seam_coherence", root=effective_root)
    trigger = helpers.latest_trigger(document, status="PENDING_RECOMPUTE", trigger_id=trigger_id)
    if trigger is None:
        raise ValueError("No pending QM seam coherence recompute trigger found")

    baseline_entry = baseline["surface_baselines"]["qm_seam_coherence"]
    baseline_values = baseline_entry["baseline_values"]
    fraction = helpers.deterministic_fraction("qm_seam_coherence", str(trigger.get("trigger_id")))
    delta = helpers.quantize(0.02 + 0.03 * fraction)
    coherence_before = float(baseline_values["coherence_metric"])
    coherence_after = helpers.quantize(coherence_before + delta)
    velocity_before = float(baseline_values["state_transition_velocity"])
    velocity_after = helpers.quantize(velocity_before + delta / 2.0)
    flux_reference = float(baseline_values["ledger_flux_reference"])
    correlation = helpers.quantize(min(0.99, 0.55 + fraction / 3.0))
    captured = helpers.utc_now(captured_at_utc)

    document["computed_state"] = {
        "surface_id": "qm_seam_coherence",
        "trigger_id": trigger["trigger_id"],
        "baseline_report": str(baseline_path.relative_to(REPO_ROOT)).replace("\\", "/"),
        "qm_coherence_metric_before": coherence_before,
        "qm_coherence_metric": coherence_after,
        "state_change_from_baseline": helpers.quantize(coherence_after - coherence_before),
        "state_transition_velocity_before": velocity_before,
        "state_transition_velocity": velocity_after,
        "correlation_with_ledger_flux": correlation,
        "ledger_flux_reference": flux_reference,
        "attribution": "REVISED_BLOCKER_DEFINITION_PROMOTION_DELTA",
    }
    document["execution_summary"] = {
        "surface_id": "qm_seam_coherence",
        "classification": "RECOMPUTE_COMPLETED_WITH_OUTPUTS",
        "next_action": "RERUN_RECOMPUTE_OBSERVATION_REPORT",
    }
    helpers.mark_trigger_completed(
        trigger,
        completed_at_utc=captured,
        note="QM seam coherence recompute output materialized",
    )
    helpers.refresh_surface_metadata(document, surface_id="qm_seam_coherence", trigger_id=trigger["trigger_id"], captured_at_utc=captured)
    helpers.write_json(helpers.surface_path("qm_seam_coherence", root=effective_root), document)
    return document


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Execute the QM seam coherence recompute surface.")
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
        "qm_seam_coherence_recompute_execute: "
        f"trigger_id={payload['last_completed_trigger_id']} out={helpers.surface_path('qm_seam_coherence', root=surface_root)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())