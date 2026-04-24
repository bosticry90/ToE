from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import authority_surface_parity_check as authority_parity
from formal.python.tools import physics_math_throughput_baseline_snapshot as throughput_baseline
from formal.python.tools import repo_recovery_baseline_report as recovery_baseline
from formal.python.tools import ws10_t42_redteam_baseline_freeze_report as ws10_t42
from formal.python.tools import ws10_t43_maintenance_selection_report as ws10_t43
from formal.python.tools import ws10_t44_qm_stat_direct_cycle_consolidation_report as ws10_t44
from formal.python.tools import ws10_t45_operator_truth_pack_report as ws10_t45
from formal.python.tools import ws10_t46_qm_stat_synthesis_gate_consolidation_report as ws10_t46
from formal.python.tools import ws10_t47_qft_gr_release_family_summary_views_report as ws10_t47
from formal.python.tools import ws10_t48_maintenance_reduction_rollup_report as ws10_t48
from formal.python.tools import ws10_t49_post_maintenance_handoff_report as ws10_t49
from formal.python.tools import ws10_t50_post_plan_phase3_to_phase6_alignment_report as ws10_t50
from formal.python.tools import ws10_t51_post_plan_authority_source_cutover_report as ws10_t51
from formal.python.tools import ws10_t52_whole_program_acceptance_review_report as ws10_t52


REPO_ROOT = find_repo_root(Path(__file__))


def _read_json_if_exists(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def _existing_timestamp(path: Path, *keys: str) -> str | None:
    payload = _read_json_if_exists(path)
    if payload is None:
        return None
    for key in keys:
        value = payload.get(key)
        if isinstance(value, str) and value:
            return value
    return None


def _write_json_if_changed(path: Path, payload: dict[str, Any], *, check: bool, changes: list[str]) -> None:
    text = json.dumps(payload, indent=2) + "\n"
    current = path.read_text(encoding="utf-8") if path.exists() else None
    if current == text:
        return
    changes.append(str(path.relative_to(REPO_ROOT)).replace("\\", "/"))
    if not check:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


def _refresh_default_report(module: Any, *, check: bool, changes: list[str]) -> None:
    path = module.DEFAULT_OUT_PATH
    captured_at_utc = _existing_timestamp(path, "captured_at_utc")
    payload = module.build_report(captured_at_utc=captured_at_utc)
    _write_json_if_changed(path, payload, check=check, changes=changes)


def refresh_all(*, check: bool) -> list[str]:
    changes: list[str] = []

    roadmap_before = authority_parity.ROADMAP_PATH.read_text(encoding="utf-8")
    roadmap_after = authority_parity.generate_synced_roadmap_content(
        authority_parity.STATE_PATH.read_text(encoding="utf-8"),
        roadmap_before,
    )
    if roadmap_after != roadmap_before:
        changes.append(str(authority_parity.ROADMAP_PATH.relative_to(REPO_ROOT)).replace("\\", "/"))
        if not check:
            authority_parity.ROADMAP_PATH.write_text(roadmap_after, encoding="utf-8")

    throughput_payload = throughput_baseline.build_snapshot_payload(
        generated_at_utc=_existing_timestamp(throughput_baseline.DEFAULT_REPORT_PATH, "generated_at_utc")
    )
    _write_json_if_changed(
        throughput_baseline.DEFAULT_REPORT_PATH,
        throughput_payload,
        check=check,
        changes=changes,
    )

    recovery_payload = recovery_baseline.build_report(
        captured_at_utc=_existing_timestamp(recovery_baseline.DEFAULT_OUT_PATH, "captured_at_utc"),
        lastfailed_snapshot=(_read_json_if_exists(recovery_baseline.DEFAULT_OUT_PATH) or {})
        .get("branch_health_baseline", {})
        .get("lastfailed_snapshot"),
    )
    _write_json_if_changed(recovery_baseline.DEFAULT_OUT_PATH, recovery_payload, check=check, changes=changes)

    t42_path = ws10_t42.DEFAULT_OUT_PATH
    t42_existing = _read_json_if_exists(t42_path) or {}
    t42_payload = ws10_t42.build_report(
        captured_at_utc=t42_existing.get("captured_at_utc"),
        anchored_commit=t42_existing.get("anchored_commit"),
    )
    _write_json_if_changed(t42_path, t42_payload, check=check, changes=changes)

    t43_registry_path = ws10_t43.DEFAULT_REGISTRY_PATH
    t43_checkpoint_path = ws10_t43.DEFAULT_CHECKPOINT_PATH
    t43_registry_payload = ws10_t43.build_release_family_registry(
        captured_at_utc=_existing_timestamp(t43_registry_path, "captured_at_utc")
    )
    _write_json_if_changed(t43_registry_path, t43_registry_payload, check=check, changes=changes)
    t43_checkpoint_payload = ws10_t43.build_checkpoint(
        registry=t43_registry_payload,
        captured_at_utc=_existing_timestamp(t43_checkpoint_path, "captured_at_utc"),
    )
    _write_json_if_changed(t43_checkpoint_path, t43_checkpoint_payload, check=check, changes=changes)

    for module in [ws10_t44, ws10_t45, ws10_t46, ws10_t47, ws10_t48, ws10_t49, ws10_t50, ws10_t51, ws10_t52]:
        _refresh_default_report(module, check=check, changes=changes)

    return changes


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Refresh generator-backed recovery artifacts and derived roadmap surfaces.")
    parser.add_argument(
        "--check",
        action="store_true",
        help="Do not write files; exit nonzero if any refreshed output would change.",
    )
    ns = parser.parse_args(argv)

    changes = refresh_all(check=ns.check)
    if changes:
        print("recovery_artifact_refresh: changed")
        for path in changes:
            print(f"- {path}")
        return 1 if ns.check else 0

    print("recovery_artifact_refresh: clean")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
