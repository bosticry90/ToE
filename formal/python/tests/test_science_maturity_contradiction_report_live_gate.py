from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "science_maturity_contradiction_report_20260416_v0.json"
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_MATURITY_CONTRADICTION_REPORT_POLICY_20260416_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

REFS = (
    "formal/docs/release/SCIENCE_MATURITY_CONTRADICTION_REPORT_POLICY_20260416_v0.md",
    "formal/output/reports/science_maturity_contradiction_report_20260416_v0.json",
    "formal/python/tests/test_science_maturity_contradiction_report_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_science_maturity_contradiction_report_live_surface_is_consistent() -> None:
    payload = _read_json(REPORT_PATH)
    assert payload.get("schema_id") == "SCIENCE_MATURITY_CONTRADICTION_REPORT_20260416_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"
    assert payload.get("contradiction_status") == "FAIL_CLOSED_CONTRADICTIONS_PRESENT"

    summary = payload.get("summary", {})
    assert summary.get("contradictions_total") == 9
    assert summary.get("highest_severity") == "HIGH"
    assert summary.get("active_stale_ready_rows") == 9
    assert summary.get("live_blocker_state_change") == "NO_DELTA_DETECTED_ROUTE_TO_REWORK"
    assert summary.get("live_progress_classification") == "REWORK_ROUTED"

    contradiction_types = set(summary.get("contradiction_types_present", []))
    assert "PILLAR_M4_COMPLETE_VS_LIVE_THEOREM_GAP" in contradiction_types
    assert "SEAM_PHYSICS_COMPLETE_VS_LIVE_HOLD_OR_PARITY" in contradiction_types
    assert "SEAM_GOVERNANCE_COMPLETE_VS_PHYSICS_INCOMPLETE" not in contradiction_types
    assert "LIVE_SEAM_ROW_MISSING_CANONICAL_STATUS" not in contradiction_types
    assert "STALE_READINESS_SIGNAL_WITH_PATHS_PINNED" in contradiction_types

    contradictions = payload.get("contradictions", [])
    pillar_rows = [entry for entry in contradictions if entry.get("contradiction_type") == "PILLAR_M4_COMPLETE_VS_LIVE_THEOREM_GAP"]
    assert len(pillar_rows) == 7
    seam_rows = [entry for entry in contradictions if entry.get("contradiction_type") == "SEAM_PHYSICS_COMPLETE_VS_LIVE_HOLD_OR_PARITY"]
    assert len(seam_rows) == 1
    split_rows = [entry for entry in contradictions if entry.get("contradiction_type") == "SEAM_GOVERNANCE_COMPLETE_VS_PHYSICS_INCOMPLETE"]
    assert split_rows == []
    missing_rows = [entry for entry in contradictions if entry.get("contradiction_type") == "LIVE_SEAM_ROW_MISSING_CANONICAL_STATUS"]
    assert missing_rows == []

    stale_rows = [entry for entry in contradictions if entry.get("contradiction_type") == "STALE_READINESS_SIGNAL_WITH_PATHS_PINNED"]
    assert len(stale_rows) == 1
    assert "ROW-SEAM-QFT-GR-001" not in stale_rows[0]["row_ids"]
    assert "ROW-SEAM-GR-QM-001" not in stale_rows[0]["row_ids"]


def test_science_maturity_contradiction_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    policy_text = _read(POLICY_PATH)

    assert "formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json" in policy_text
    assert "formal/output/reports/blocker_burn_dashboard_20260416_v0.json" in policy_text
    assert "formal/output/reports/physics_progress_ledger_v0.json" in policy_text

    for ref in REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )