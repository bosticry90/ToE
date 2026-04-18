from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "BLOCKER_BURN_DASHBOARD_POLICY_20260416_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

REPORT_REFS = (
    "formal/docs/release/BLOCKER_BURN_DASHBOARD_POLICY_20260416_v0.md",
    "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
    "formal/python/tests/test_blocker_burn_dashboard_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_blocker_burn_dashboard_live_report_is_consistent() -> None:
    payload = _read_json(REPORT_PATH)

    assert payload.get("schema_id") == "BLOCKER_BURN_DASHBOARD_20260416_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"

    scoreboard = payload.get("blocker_scoreboard", {})
    assert scoreboard.get("current", {}).get("THEOREM_GAP") == 7
    assert scoreboard.get("current", {}).get("SEAM_INTEGRATION_GAP") == 3
    assert scoreboard.get("current", {}).get("PARITY_DRIFT") == 0
    assert scoreboard.get("net_delta") == -1
    assert scoreboard.get("movement_status") == "DECREASING"
    assert scoreboard.get("exception_required") is False

    row_contrib = payload.get("row_blocker_contributions", {})
    assert row_contrib.get("rows_total") == 10
    assert row_contrib.get("blocker_classes", {}).get("THEOREM_GAP", {}).get("row_count") == 7
    assert row_contrib.get("blocker_classes", {}).get("SEAM_INTEGRATION_GAP", {}).get("row_count") == 3
    assert row_contrib.get("blocker_classes", {}).get("PARITY_DRIFT", {}).get("row_count") == 0

    readiness = payload.get("row_promotion_readiness", {})
    assert readiness.get("rows_total") == 11
    assert readiness.get("rows_with_all_paths_pinned") == 11
    assert readiness.get("rows_with_runtime_state_visible") == 11
    assert readiness.get("rows_missing_canonical_path") == 0
    assert readiness.get("report_scope_boundary") == (
        "DASHBOARD_REPORTS_PATH_AND_RUNTIME_STATE_READINESS_ONLY_AND_DOES_NOT_ASSERT_GATE_PASSING"
    )

    readiness_rows = {entry["row_id"]: entry for entry in readiness.get("rows", [])}
    assert readiness_rows["ROW-SEAM-GR-QM-001"]["governance_checkpoint_status"] == "GOVERNANCE_COMPLETE"
    assert readiness_rows["ROW-SEAM-GR-QM-001"]["physics_checkpoint_status"] == "PHYSICS_COMPLETE"
    assert readiness_rows["ROW-SEAM-GR-QM-001"]["gate_runtime_status"] == "GATE_RUNTIME_RECOMPUTE_MONITORING_REQUIRED"
    assert readiness_rows["ROW-PILLAR-EM-001"]["governance_checkpoint_status"] == "NOT_APPLICABLE_PILLAR_ROW"
    assert readiness_rows["ROW-PILLAR-EM-001"]["physics_checkpoint_status"] == "THEOREM_GAP_OPEN"
    assert readiness_rows["ROW-PILLAR-EM-001"]["gate_runtime_status"] == "PATH_PINNED_RUNTIME_NOT_YET_RECORDED"

    closure_linkage = payload.get("closure_map_linkage", {})
    assert closure_linkage.get("rows_total") == 11
    assert closure_linkage.get("missing_owner_rows") == []

    timeline = payload.get("tranche_timeline", {})
    assert timeline.get("current_tranche_id") == "TGC-76"
    assert timeline.get("row_promotion_count") == 0
    assert timeline.get("ledger_progress_classification") == "PROGRESS"

    freshness = payload.get("source_freshness", {})
    assert freshness.get("stale_input_warning") is True
    stale_sources = set(freshness.get("stale_sources", []))
    assert "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md" in stale_sources
    assert "formal/output/reports/convergence_baseline_pack_20260409_v0.json" in stale_sources


def test_blocker_burn_dashboard_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    policy_text = _read(POLICY_PATH)

    assert "formal/output/reports/governance_blocker_trend_window_20260410_v0.json" in policy_text
    assert "formal/output/reports/physics_progress_ledger_v0.json" in policy_text

    for ref in REPORT_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )