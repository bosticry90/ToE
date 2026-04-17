from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_GOVERNANCE_BUDGET_POLICY_20260416_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "science_governance_budget_20260416_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

REFS = (
    "formal/docs/release/SCIENCE_GOVERNANCE_BUDGET_POLICY_20260416_v0.md",
    "formal/output/reports/science_governance_budget_20260416_v0.json",
    "formal/python/tests/test_science_governance_budget_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_science_governance_budget_live_report_is_consistent() -> None:
    payload = _read_json(REPORT_PATH)
    assert payload.get("schema_id") == "SCIENCE_GOVERNANCE_BUDGET_20260416_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"

    counts = payload.get("representative_surface_counts", {})
    assert counts.get("science_core_rows") == 7
    assert counts.get("governance_control_rows") == 4
    assert counts.get("science_to_control_ratio") == 1.75

    coupling = payload.get("dashboard_coupling", {})
    assert coupling.get("movement_status") == "FLAT"
    assert coupling.get("net_delta") == 0
    assert coupling.get("exception_required") is True
    assert coupling.get("stale_input_warning") is True

    posture = payload.get("budget_posture", {})
    assert posture.get("budget_posture") == "SCIENCE_REBALANCE_REVIEW_REQUIRED"


def test_science_governance_budget_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    policy_text = _read(POLICY_PATH)

    assert "formal/output/reports/blocker_burn_dashboard_20260416_v0.json" in policy_text
    assert "formal/docs/paper/SCIENTIFIC_CORE_INDEX_v0.md" in policy_text

    for ref in REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )