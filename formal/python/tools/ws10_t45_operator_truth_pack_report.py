from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "WS10_T45_OPERATOR_TRUTH_PACK_REPORT_20260418_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_operator_truth_pack_20260418_v0.json"
T42_PATH = REPO_ROOT / "formal" / "output" / "ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0.json"
T43_PATH = REPO_ROOT / "formal" / "output" / "ws10_t43_maintenance_selection_checkpoint_20260418_v0.json"
T44_PATH = REPO_ROOT / "formal" / "output" / "ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0.json"
QFT_REGISTRY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_sliceb_increment_family_registry_20260418_v0.json"
BLOCKER_DASHBOARD_PATH = REPO_ROOT / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json"
SEAM_LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
COMPLETION_MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, captured_at_utc: str | None = None) -> dict[str, Any]:
    t42 = _read_json(T42_PATH)
    t43 = _read_json(T43_PATH)
    t44 = _read_json(T44_PATH)
    qft_registry = _read_json(QFT_REGISTRY_PATH)
    blocker = _read_json(BLOCKER_DASHBOARD_PATH)
    seam = _read_json(SEAM_LEDGER_PATH)
    blocker_current = blocker.get("blocker_scoreboard", {}).get("current", {})
    seam_summary = seam.get("summary", {})

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "ws10_operator_truth_pack_20260418_v0",
        "status": "NONAUTHORITATIVE_OPERATOR_REVIEW_PACKET_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "operator_boundary": {
            "authority_status": "SUMMARY_ONLY",
            "required_canonical_reads": [
                _ptr(BLOCKER_DASHBOARD_PATH),
                _ptr(SEAM_LEDGER_PATH),
                _ptr(ROADMAP_PATH),
                _ptr(INVENTORY_PATH),
                _ptr(COMPLETION_MATRIX_PATH),
            ],
            "non_claim_boundary": "This operator pack summarizes already-pinned repository state and points back to canonical surfaces. It does not create new scientific authority or alter live release truth.",
        },
        "tranche_stack": {
            "t42_checkpoint": _ptr(T42_PATH),
            "t43_checkpoint": _ptr(T43_PATH),
            "t44_checkpoint": _ptr(T44_PATH),
            "t42_primary_metrics": t42.get("baseline_metrics", {}),
            "t43_selected_gate_family": t43.get("selected_gate_family", {}),
            "t43_selected_release_family": t43.get("selected_release_family", {}),
            "t44_reduction_metrics": t44.get("consolidation_metrics", {}),
        },
        "current_control_snapshot": {
            "active_theorem_gap_count": int(blocker_current.get("THEOREM_GAP", 0)),
            "active_seam_gap_count": int(blocker_current.get("SEAM_INTEGRATION_GAP", 0)),
            "active_parity_drift_count": int(blocker_current.get("PARITY_DRIFT", 0)),
            "blocker_net_delta": int(blocker.get("blocker_scoreboard", {}).get("net_delta", 0)),
            "blocker_movement_status": blocker.get("blocker_scoreboard", {}).get("movement_status"),
            "active_review_rows": int(seam_summary.get("active_review_rows", 0)),
            "external_hold_rows": int(seam_summary.get("external_hold_rows", 0)),
            "held_review_rows": int(seam_summary.get("held_review_rows", 0)),
        },
        "review_focus": {
            "active_gate_reduction_lane": "QM_STAT_DIRECT_CYCLE_GATES",
            "next_gate_reduction_lane": "QM_STAT_SYNTHESIS_GATES",
            "indexed_release_family": {
                "family_id": qft_registry.get("family_id"),
                "file_count": int(qft_registry.get("file_count", 0)),
                "registry_pointer": _ptr(QFT_REGISTRY_PATH),
            },
        },
        "summary": {
            "terminal_outcome": "OPERATOR_TRUTH_PACK_GENERATED_OVER_T42_T43_T44_AND_CONTROL_SURFACES",
            "next_action": "CONSOLIDATE_QM_STAT_SYNTHESIS_GATES_AND_EXTEND_RELEASE_FAMILY_SUMMARY_VIEWS",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T45 operator truth-pack report.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    args = parser.parse_args()

    report = build_report()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()