from __future__ import annotations

import argparse
from pathlib import Path

from formal.python.tools import blocker_authority_transport_recompute_execute
from formal.python.tools import ledger_artifact_transport_recompute_execute
from formal.python.tools import qm_seam_coherence_recompute_execute
from formal.python.tools import recompute_baseline_snapshot
from formal.python.tools import recompute_surface_helpers as helpers


REPO_ROOT = helpers.REPO_ROOT
DEFAULT_BASELINE_PATH = helpers.BASELINE_REPORT_PATH
DEFAULT_EXECUTION_MODE = "dry-run"
LIVE_WRITEBACK_MODE = "live-writeback"
LIVE_WRITEBACK_REQUIREMENT = "EXPLICIT_ALLOW_LIVE_WRITEBACK_TRUE"
BUNDLE_NEXT_ACTION = "RERUN_RECOMPUTE_OBSERVATION_REPORT"
DEFAULT_DRY_RUN_ROOT = REPO_ROOT / "formal" / "output" / "recompute_dry_run" / "latest"


def dry_run_baseline_path(root: Path) -> Path:
    return root / "formal" / "output" / "reports" / "recompute_baseline_snapshot_20260418_v0.json"


def dry_run_bundle_report_path(root: Path) -> Path:
    return root / "formal" / "output" / "reports" / "recompute_execution_bundle_20260418_v0.json"


def execute_all(
    *,
    baseline_path: Path | None,
    captured_at_utc: str | None,
    execution_mode: str = DEFAULT_EXECUTION_MODE,
    allow_live_writeback: bool = False,
    surface_root: Path | None = None,
) -> dict:
    if execution_mode not in {DEFAULT_EXECUTION_MODE, LIVE_WRITEBACK_MODE}:
        raise ValueError(f"Unsupported execution mode: {execution_mode}")
    if execution_mode == LIVE_WRITEBACK_MODE and not allow_live_writeback:
        raise ValueError(LIVE_WRITEBACK_REQUIREMENT)

    effective_surface_root: Path
    effective_baseline_path: Path
    bundle_report_path: Path
    copied_surfaces: list[str] = []
    live_writeback_performed = execution_mode == LIVE_WRITEBACK_MODE

    if execution_mode == DEFAULT_EXECUTION_MODE:
        effective_surface_root = helpers.resolve_root(surface_root or DEFAULT_DRY_RUN_ROOT)
        copied_surfaces = helpers.clone_recompute_surfaces(destination_root=effective_surface_root)
        effective_baseline_path = baseline_path or dry_run_baseline_path(effective_surface_root)
        bundle_report_path = dry_run_bundle_report_path(effective_surface_root)
    else:
        effective_surface_root = helpers.resolve_root(surface_root)
        effective_baseline_path = baseline_path or DEFAULT_BASELINE_PATH
        bundle_report_path = effective_surface_root / "formal" / "output" / "reports" / "recompute_execution_bundle_20260418_v0.json"

    baseline_payload = recompute_baseline_snapshot.build_report(captured_at_utc=captured_at_utc)
    helpers.write_json(effective_baseline_path, baseline_payload)

    qm_payload = qm_seam_coherence_recompute_execute.execute_surface(
        baseline_path=effective_baseline_path,
        trigger_id=None,
        captured_at_utc=captured_at_utc,
        surface_root=effective_surface_root,
    )
    ledger_payload = ledger_artifact_transport_recompute_execute.execute_surface(
        baseline_path=effective_baseline_path,
        trigger_id=None,
        captured_at_utc=captured_at_utc,
        surface_root=effective_surface_root,
    )
    authority_payload = blocker_authority_transport_recompute_execute.execute_surface(
        baseline_path=effective_baseline_path,
        trigger_id=None,
        captured_at_utc=captured_at_utc,
        surface_root=effective_surface_root,
    )

    payload = {
        "schema_id": "RECOMPUTE_EXECUTION_BUNDLE_REPORT_20260418_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": helpers.utc_now(captured_at_utc),
        "summary": {
            "execution_mode": execution_mode,
            "baseline_report": str(effective_baseline_path.relative_to(effective_surface_root if execution_mode == DEFAULT_EXECUTION_MODE else REPO_ROOT)).replace("\\", "/"),
            "surfaces_completed": 3,
            "live_writeback_performed": live_writeback_performed,
            "next_action": BUNDLE_NEXT_ACTION,
        },
        "dry_run_workspace": {
            "workspace_root": str(effective_surface_root.relative_to(REPO_ROOT)).replace("\\", "/") if execution_mode == DEFAULT_EXECUTION_MODE else None,
            "copied_surfaces": copied_surfaces,
        },
        "surface_outputs": {
            "qm_seam_coherence": qm_payload.get("last_completed_trigger_id"),
            "ledger_artifact_transport": ledger_payload.get("last_completed_trigger_id"),
            "blocker_authority_transport": authority_payload.get("last_completed_trigger_id"),
        },
    }
    helpers.write_json(bundle_report_path, payload)
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Execute all bounded recompute surfaces.")
    parser.add_argument("--baseline", type=Path, default=None)
    parser.add_argument("--captured-at-utc", default=None)
    parser.add_argument("--execution-mode", choices=[DEFAULT_EXECUTION_MODE, LIVE_WRITEBACK_MODE], default=DEFAULT_EXECUTION_MODE)
    parser.add_argument("--allow-live-writeback", action="store_true")
    parser.add_argument("--surface-root", type=Path, default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    baseline_path = None if ns.baseline is None else (ns.baseline if ns.baseline.is_absolute() else (REPO_ROOT / ns.baseline))
    surface_root = None if ns.surface_root is None else (ns.surface_root if ns.surface_root.is_absolute() else (REPO_ROOT / ns.surface_root))
    payload = execute_all(
        baseline_path=baseline_path,
        captured_at_utc=ns.captured_at_utc,
        execution_mode=ns.execution_mode,
        allow_live_writeback=ns.allow_live_writeback,
        surface_root=surface_root,
    )
    print(
        "recompute_execute_all: "
        f"mode={payload['summary']['execution_mode']} surfaces_completed={payload['summary']['surfaces_completed']} next_action={payload['summary']['next_action']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())