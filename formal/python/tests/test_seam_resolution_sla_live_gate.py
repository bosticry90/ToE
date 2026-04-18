from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SEAM_RESOLUTION_SLA_POLICY_20260416_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json"
CONTRADICTION_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_MATURITY_CONTRADICTION_REPORT_POLICY_20260416_v0.md"
CONTRADICTION_REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "science_maturity_contradiction_report_20260416_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

REFS = (
    "formal/docs/release/SEAM_RESOLUTION_SLA_POLICY_20260416_v0.md",
    "formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json",
    "formal/python/tests/test_seam_resolution_sla_live_gate.py",
    "formal/docs/release/SCIENCE_MATURITY_CONTRADICTION_REPORT_POLICY_20260416_v0.md",
    "formal/output/reports/science_maturity_contradiction_report_20260416_v0.json",
    "formal/python/tests/test_science_maturity_contradiction_report_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_seam_resolution_sla_live_report_is_consistent() -> None:
    payload = _read_json(REPORT_PATH)
    assert payload.get("schema_id") == "SEAM_RESOLUTION_SLA_LEDGER_20260416_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"

    policy = payload.get("policy", {})
    assert policy.get("decision_owner_role") == "WS_10_LANE_AUTHORITY_OWNER"
    assert policy.get("active_lane_review_hours") == 24
    assert policy.get("held_lane_review_hours") == 168
    assert policy.get("escalation_after_windows") == 2
    assert policy.get("decision_owner_assignment_status") == "NAMED_OWNERS_ASSIGNED"

    summary = payload.get("summary", {})
    assert summary.get("seam_rows_total") == 4
    assert summary.get("active_review_rows") == 2
    assert summary.get("held_review_rows") == 2
    assert summary.get("external_hold_rows") == 1
    assert summary.get("split_completion_rows") == 0
    assert summary.get("missing_owner_rows") == []
    assert summary.get("owner_completion_rate") == 1.0
    assert summary.get("missing_seam_status_rows") == []
    assert summary.get("seam_status_coverage_rate") == 1.0

    entries = {entry["row_id"]: entry for entry in payload.get("entries", [])}
    assert entries["ROW-SEAM-QFT-GR-001"]["decision_state"] == "HOLD_RETAINED_EXTERNAL_HOLD_RELEASE_REQUIRED"
    assert entries["ROW-SEAM-QFT-GR-001"]["row_activity_classification"] == "HELD_EXTERNAL"
    assert entries["ROW-SEAM-QFT-GR-001"]["is_external_hold"] is True
    assert entries["ROW-SEAM-QFT-GR-001"]["gate_runtime_status"] == "PATH_PINNED_RUNTIME_PENDING_BRANCH_EXCEPTION"
    assert entries["ROW-SEAM-GR-QM-001"]["decision_state"] == "CLOSED_RECOMPUTE_MONITORING_REQUIRED"
    assert entries["ROW-SEAM-GR-QM-001"]["row_activity_classification"] == "CLOSED_MONITORING"
    assert entries["ROW-SEAM-GR-QM-001"]["seam_id"] == "SEAM-GR-QM"
    assert entries["ROW-SEAM-GR-QM-001"]["seam_class"] == "A"
    assert entries["ROW-SEAM-GR-QM-001"]["governance_complete"] is True
    assert entries["ROW-SEAM-GR-QM-001"]["physics_complete"] is True
    assert entries["ROW-SEAM-GR-QM-001"]["seam_status_resolution"] == "CANONICAL_SEAM_STATUS_PINNED"
    assert entries["ROW-SEAM-QM-STAT-001"]["seam_class"] == "B"
    assert entries["ROW-SEAM-QM-STAT-001"]["governance_complete"] is False
    assert entries["ROW-SEAM-QM-STAT-001"]["decision_state"] == "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION"
    assert entries["ROW-SEAM-QM-STAT-001"]["row_activity_classification"] == "ACTIVE_TRACKED"
    assert entries["ROW-SEAM-QFT-GR-001"]["primary_owner"] == "TEAM_SEAM_QFT_GR"
    assert entries["ROW-SEAM-QFT-GR-001"]["secondary_owner"] == "TEAM_GOVERNANCE_CORE"
    assert entries["ROW-SEAM-QFT-GR-001"]["seam_id"] == "SEAM-QFT-GR"
    assert entries["ROW-SEAM-QFT-GR-001"]["seam_class"] == "B"
    assert entries["ROW-SEAM-QFT-GR-001"]["witness_route_status"] == "HOLD_FOR_SCALAR_PUBLICATION_v0"
    assert entries["ROW-SEAM-QFT-GR-001"]["governance_complete"] is False
    assert entries["ROW-SEAM-QFT-GR-001"]["physics_complete"] is False
    assert entries["ROW-SEAM-QFT-GR-001"]["seam_status_read"] == "CLASS_B_HELD_FOR_SCALAR_PUBLICATION_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE"
    assert entries["ROW-SEAM-QFT-GR-001"]["seam_status_resolution"] == "CANONICAL_SEAM_STATUS_PINNED"
    assert entries["ROW-SEAM-QFT-GR-001"]["required_evidence_surface"] == "formal/docs/paper/TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
    assert entries["ROW-SEAM-QFT-GR-001"]["next_review_due_utc"]
    assert entries["ROW-SEAM-QFT-GR-001"]["escalation_due_utc"]
    assert entries["ROW-SEAM-GR-QM-001"]["primary_owner"] == "TEAM_SEAM_GR_QM"

    coupling = payload.get("dashboard_coupling", {})
    assert coupling.get("movement_status") == "FLAT"
    assert coupling.get("exception_required") is True
    assert coupling.get("stale_input_warning") is True


def test_seam_resolution_sla_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    policy_text = _read(POLICY_PATH)
    contradiction_policy_text = _read(CONTRADICTION_POLICY_PATH)
    contradiction_report = _read_json(CONTRADICTION_REPORT_PATH)

    assert "formal/output/reports/blocker_burn_dashboard_20260416_v0.json" in policy_text
    assert "formal/docs/release/WS_10_PACKET41_PACKET42_HOLD_RECONSIDERATION_POLICY_20260408_v0.md" in policy_text
    assert "formal/docs/release/GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json" in policy_text
    assert "formal/output/reports/science_maturity_contradiction_report_20260416_v0.json" in policy_text
    assert contradiction_report.get("schema_id") == "SCIENCE_MATURITY_CONTRADICTION_REPORT_20260416_v0"
    assert "formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json" in contradiction_policy_text

    for ref in REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )