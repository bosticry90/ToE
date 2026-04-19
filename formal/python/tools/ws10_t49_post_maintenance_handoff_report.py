from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.post_plan_physics_advancement_target_map_report import _parse_markdown_table


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "WS10_T49_POST_MAINTENANCE_HANDOFF_REPORT_20260418_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_t49_post_maintenance_handoff_20260418_v0.json"
T48_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_maintenance_reduction_rollup_20260418_v0.json"
TARGET_MAP_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json"
COSMO_TRANCHE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json"
POST_PLAN_PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"
COMPLETION_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, captured_at_utc: str | None = None) -> dict[str, Any]:
    t48 = _read_json(T48_PATH)
    target_map = _read_json(TARGET_MAP_PATH)
    cosmo_tranche = _read_json(COSMO_TRANCHE_PATH)
    _read_text(POST_PLAN_PROGRAM_PATH)

    matrix_rows = _parse_markdown_table(
        _read_text(COMPLETION_MATRIX_PATH),
        [
            "row_id",
            "domain",
            "lane",
            "current_status",
            "blocker_class",
            "primary_target",
            "primary_artifact",
            "primary_gate",
            "governance_checkpoint_status",
            "physics_checkpoint_status",
            "gate_runtime_status",
        ],
    )
    row_map = {row["row_id"]: row for row in matrix_rows}
    routed_rows = {row["row_id"]: row for row in target_map.get("routed_rows", [])}

    t48_defaults = t48.get("execution_window_defaults", {})
    cosmo_row = row_map.get("ROW-SEAM-COSMO-SR-001", {})
    qm_row = row_map.get("ROW-SEAM-QM-STAT-001", {})
    cosmo_route = routed_rows.get("ROW-SEAM-COSMO-SR-001", {})
    qm_route = routed_rows.get("ROW-SEAM-QM-STAT-001", {})
    qft_route = routed_rows.get("ROW-SEAM-QFT-GR-001", {})

    t48_defaults_ok = (
        t48_defaults.get("operator_review_surface", {}).get("artifact_pointer")
        == "formal/output/reports/ws10_operator_truth_pack_20260418_v0.json"
        and t48_defaults.get("release_family_review_surface", {}).get("artifact_pointer")
        == "formal/output/reports/qft_gr_sliceb_increment_family_summary_views_20260418_v0.json"
    )
    target_map_ok = (
        target_map.get("summary", {}).get("terminal_outcome")
        == "POST_PLAN_PHYSICS_ADVANCEMENT_TARGET_MAP_MATERIALIZED"
        and target_map.get("summary", {}).get("executable_now_rows") == ["ROW-SEAM-COSMO-SR-001"]
        and cosmo_route.get("route_class") == "EXECUTABLE_NOW"
        and qm_route.get("route_class") == "BLOCKED_PENDING_AUTHORITY"
        and qft_route.get("route_class") == "EXTERNAL_HOLD"
    )
    cosmo_tranche_ok = cosmo_tranche.get("summary", {}).get("terminal_outcome") in {
        "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_NONPROMOTED",
        "POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_EXECUTED_AND_PROMOTED",
    }
    handoff_ok = (
        cosmo_tranche.get("summary", {}).get("target_row_id") == "ROW-SEAM-COSMO-SR-001"
        and cosmo_tranche.get("summary", {}).get("next_action")
        == "RETAIN_COSMO_SR_AS_SOLE_EXECUTABLE_ROW_AND_REQUIRE_NEW_ROW_MOVEMENT_BEFORE_REROUTE"
    )
    matrix_alignment_ok = (
        bool(cosmo_row)
        and bool(qm_row)
        and cosmo_row.get("row_id") == "ROW-SEAM-COSMO-SR-001"
        and qm_row.get("row_id") == "ROW-SEAM-QM-STAT-001"
        and cosmo_row.get("gate_runtime_status") == "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION"
        and qm_row.get("gate_runtime_status") == "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION"
    )

    all_ok = all([t48_defaults_ok, target_map_ok, cosmo_tranche_ok, handoff_ok, matrix_alignment_ok])
    terminal_outcome = (
        "WS10_POST_MAINTENANCE_HANDOFF_TO_POST_PLAN_EXECUTION_PINNED_NONLIVE_v0"
        if all_ok
        else "WS10_POST_MAINTENANCE_HANDOFF_EVIDENCE_INCOMPLETE_v0"
    )

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "ws10_t49_post_maintenance_handoff_20260418_v0",
        "status": "ACTIVE_POST_MAINTENANCE_HANDOFF_NONLIVE_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "t48_review_defaults_pinned": t48_defaults_ok,
            "post_plan_target_map_materialized": target_map_ok,
            "post_plan_cosmo_sr_tranche_materialized": cosmo_tranche_ok,
            "handoff_next_action_preserved": handoff_ok,
            "completion_matrix_alignment_ok": matrix_alignment_ok,
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": all_ok,
                "single_outcome_materialized": True,
                "single_executable_row_preserved": target_map_ok,
                "blocked_qm_stat_path_preserved": qm_route.get("route_class") == "BLOCKED_PENDING_AUTHORITY",
            },
            "inputs": {
                "operator_review_surface": t48_defaults.get("operator_review_surface", {}).get("artifact_pointer"),
                "release_review_surface": t48_defaults.get("release_family_review_surface", {}).get("artifact_pointer"),
                "sole_executable_row": target_map.get("summary", {}).get("executable_now_rows"),
                "cosmo_tranche_outcome": cosmo_tranche.get("summary", {}).get("terminal_outcome"),
                "cosmo_tranche_next_action": cosmo_tranche.get("summary", {}).get("next_action"),
                "qm_stat_route_class": qm_route.get("route_class"),
                "qft_gr_route_class": qft_route.get("route_class"),
            },
            "summary": {
                "all_criteria_satisfied": all_ok,
                "phase_status": "COMPLETE" if all_ok else "INCOMPLETE",
                "next_action": cosmo_tranche.get("summary", {}).get(
                    "next_action",
                    "REPAIR_POST_MAINTENANCE_HANDOFF_EVIDENCE_AND_RERUN",
                ),
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "active_post_plan_program": _ptr(POST_PLAN_PROGRAM_PATH),
            "operator_review_surface": t48_defaults.get("operator_review_surface", {}).get("artifact_pointer"),
            "release_review_surface": t48_defaults.get("release_family_review_surface", {}).get("artifact_pointer"),
            "sole_executable_row": "ROW-SEAM-COSMO-SR-001",
            "blocked_authority_row": "ROW-SEAM-QM-STAT-001",
            "external_hold_row": "ROW-SEAM-QFT-GR-001",
            "cosmo_tranche_outcome": cosmo_tranche.get("summary", {}).get("terminal_outcome"),
            "next_action": cosmo_tranche.get("summary", {}).get(
                "next_action",
                "REPAIR_POST_MAINTENANCE_HANDOFF_EVIDENCE_AND_RERUN",
            ),
        },
        "source_bundle": {
            "t48_rollup": _ptr(T48_PATH),
            "post_plan_program": _ptr(POST_PLAN_PROGRAM_PATH),
            "post_plan_target_map": _ptr(TARGET_MAP_PATH),
            "post_plan_cosmo_sr_tranche": _ptr(COSMO_TRANCHE_PATH),
            "completion_matrix": _ptr(COMPLETION_MATRIX_PATH),
        },
        "non_claim_boundary": "This handoff report pins the active post-maintenance execution posture using already-materialized non-live surfaces only. It does not create new row promotion or scientific adequacy claims.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T49 post-maintenance handoff report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    ns = parser.parse_args(argv)

    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_report(captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"ws10_t49_post_maintenance_handoff_report: terminal_outcome={payload['summary']['terminal_outcome']} out={out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())