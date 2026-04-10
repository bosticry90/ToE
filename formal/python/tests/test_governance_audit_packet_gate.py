from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_20260410_v0.md"
PACKET_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_audit_packet_20260410_v0.json"

REQUIRED_BLOCKER_CLASSES = {
    "THEOREM_GAP",
    "SEAM_INTEGRATION_GAP",
    "PARITY_DRIFT",
    "GOVERNANCE_GUARDRAIL",
    "EVIDENCE_ALIGNMENT_GAP",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_governance_audit_packet_files_exist() -> None:
    assert DECLARATION_PATH.exists(), "Missing governance audit packet declaration."
    assert PACKET_PATH.exists(), "Missing governance audit packet JSON."


def test_governance_audit_packet_shape() -> None:
    payload = _json(PACKET_PATH)

    assert payload.get("schema_id") == "GOVERNANCE_AUDIT_PACKET_20260410_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"

    dimensions = payload.get("throughput_dimensions", {})
    assert set(dimensions.keys()) == {"artifact_growth", "evidence_growth", "closure_growth"}
    assert dimensions["closure_growth"].get("governance_decision_role") == "PRIMARY_GATE"

    runtime = payload.get("runtime_baselines", {})
    budget_policy = runtime.get("budget_policy", {})
    for required_key in [
        "governance_warn_seconds",
        "governance_hard_seconds",
        "branch_health_warn_seconds",
        "branch_health_hard_seconds",
    ]:
        assert required_key in budget_policy
        assert isinstance(budget_policy[required_key], (int, float))

    artifact_snapshot = payload.get("artifact_snapshot", {})
    for required_key in [
        "json_files_under_formal_output",
        "json_files_under_formal_output_reports",
        "baseline_checkpoint_count",
    ]:
        assert required_key in artifact_snapshot
        assert isinstance(artifact_snapshot[required_key], int)
        assert artifact_snapshot[required_key] >= 0

    closure_map = payload.get("closure_map", {})
    blocker_map = closure_map.get("blocker_count_by_class", {})
    assert set(blocker_map.keys()) == REQUIRED_BLOCKER_CLASSES
    rows_by_blocker = closure_map.get("rows_by_blocker_class", {})
    assert sum(rows_by_blocker.values()) == closure_map.get("rows_total")

    unresolved = closure_map.get("unresolved_blocker_classes", [])
    assert isinstance(unresolved, list)
    for item in unresolved:
        assert item in REQUIRED_BLOCKER_CLASSES

    rubric = payload.get("risk_delta_rubric", {})
    required_axes = rubric.get("required_axes", [])
    assert set(required_axes) == {
        "runtime_budget_delta",
        "artifact_growth_delta",
        "evidence_growth_delta",
        "closure_growth_delta",
    }


def test_governance_audit_packet_state_and_checklist_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "GOVERNANCE_AUDIT_PACKET_DECLARATION_v0: formal/docs/release/GOVERNANCE_AUDIT_PACKET_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_JSON_v0: formal/output/reports/governance_audit_packet_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_DIMENSION_RULE_v0: SEPARATE_ARTIFACT_GROWTH_EVIDENCE_GROWTH_AND_CLOSURE_GROWTH",
        "GOVERNANCE_AUDIT_PACKET_GATE_v0: formal/python/tests/test_governance_audit_packet_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Governance audit packet pointer declared? YES / NO",
        "Governance runtime baseline recorded? YES / NO",
        "Branch-health runtime baseline recorded? YES / NO",
        "Artifact/evidence/closure dimensions separated? YES / NO",
        "Closure-growth delta recorded? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"
