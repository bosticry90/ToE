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
    assert runtime.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_RUNTIME_BASELINE_20260410_v0.md"
    assert runtime.get("report_pointer") == "formal/output/reports/governance_runtime_baseline_20260410_v0.json"
    for runtime_key in [
        "governance_suite_seconds_baseline",
        "branch_health_full_pytest_seconds_baseline",
        "checkpoint_ladder_seconds_baseline",
    ]:
        assert isinstance(runtime.get(runtime_key), (int, float))
        assert runtime[runtime_key] > 0
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

    growth = payload.get("artifact_growth_tracking", {})
    assert growth.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_ARTIFACT_GROWTH_BASELINE_20260410_v0.md"
    assert growth.get("baseline_report_pointer") == "formal/output/reports/governance_artifact_growth_baseline_20260410_v0.json"
    assert growth.get("snapshot_report_pointer") == "formal/output/reports/governance_artifact_growth_snapshot_20260410_v0.json"
    for scope in ["baseline_counts", "current_counts", "delta_vs_baseline"]:
        values = growth.get(scope, {})
        assert isinstance(values, dict)
        for key in [
            "json_files_under_formal_output",
            "json_files_under_formal_output_reports",
        ]:
            assert key in values
            assert isinstance(values[key], int)

    lifecycle_policy = payload.get("artifact_lifecycle_policy", {})
    assert lifecycle_policy.get("declaration_pointer") == "formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.md"
    assert lifecycle_policy.get("policy_pointer") == "formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.json"
    assert isinstance(lifecycle_policy.get("retention_policy"), dict)
    assert isinstance(lifecycle_policy.get("family_rules_count"), int)
    assert lifecycle_policy.get("family_rules_count") > 0
    assert lifecycle_policy.get("family_rules_missing_archive_destination_count") == 0
    assert isinstance(lifecycle_policy.get("exemption_classes"), list)
    assert len(lifecycle_policy.get("exemption_classes")) > 0

    closure_map = payload.get("closure_map", {})
    blocker_map = closure_map.get("blocker_count_by_class", {})
    assert set(blocker_map.keys()) == REQUIRED_BLOCKER_CLASSES
    rows_by_blocker = closure_map.get("rows_by_blocker_class", {})
    assert sum(rows_by_blocker.values()) == closure_map.get("rows_total")

    unresolved = closure_map.get("unresolved_blocker_classes", [])
    assert isinstance(unresolved, list)
    for item in unresolved:
        assert item in REQUIRED_BLOCKER_CLASSES

    blocker_to_closure = closure_map.get("blocker_to_closure_map", {})
    assert blocker_to_closure.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_BLOCKER_CLOSURE_MAP_20260410_v0.md"
    assert blocker_to_closure.get("report_pointer") == "formal/output/reports/governance_blocker_closure_map_20260410_v0.json"
    assert blocker_to_closure.get("rows_total") == closure_map.get("rows_total")
    assert blocker_to_closure.get("missing_owner_rows") == []
    mappings = blocker_to_closure.get("mappings", [])
    assert isinstance(mappings, list)
    assert len(mappings) == closure_map.get("rows_total")
    for row in mappings:
        assert row.get("blocker_class") in REQUIRED_BLOCKER_CLASSES
        assert isinstance(row.get("row_id"), str) and row["row_id"]
        assert isinstance(row.get("owning_lane"), str) and row["owning_lane"]
        assert isinstance(row.get("required_closure_artifact"), str) and row["required_closure_artifact"]
        assert isinstance(row.get("required_evidence_surface"), str) and row["required_evidence_surface"]
        assert isinstance(row.get("exit_criterion"), str) and row["exit_criterion"]
        assert isinstance(row.get("closure_gate"), str) and row["closure_gate"]

    owner_assignments = closure_map.get("row_owner_assignments", [])
    assert isinstance(owner_assignments, list)
    assert len(owner_assignments) == closure_map.get("rows_total")
    for row in owner_assignments:
        assert isinstance(row.get("row_id"), str) and row["row_id"]
        assert isinstance(row.get("primary_owner"), str) and row["primary_owner"]
        assert isinstance(row.get("secondary_owner"), str) and row["secondary_owner"]
        assert isinstance(row.get("required_evidence_surface"), str) and row["required_evidence_surface"]
        assert isinstance(row.get("exit_criterion"), str) and row["exit_criterion"]

    owner_coverage = closure_map.get("owner_assignment_coverage", {})
    assert owner_coverage.get("mapped_rows") == closure_map.get("rows_total")
    assert owner_coverage.get("missing_rows") == []
    assert owner_coverage.get("coverage_ratio") == 1.0
    assert owner_coverage.get("owner_map_pointer") == (
        "formal/docs/release/GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json"
    )

    rubric = payload.get("risk_delta_rubric", {})
    required_axes = rubric.get("required_axes", [])
    assert set(required_axes) == {
        "runtime_budget_delta",
        "artifact_growth_delta",
        "evidence_growth_delta",
        "closure_growth_delta",
    }

    readiness = payload.get("promotion_readiness", {})
    assert readiness.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_PROMOTION_READINESS_SCORE_20260410_v0.md"
    assert readiness.get("report_pointer") == "formal/output/reports/governance_promotion_readiness_score_20260410_v0.json"
    score = readiness.get("readiness_score_0_to_100")
    assert isinstance(score, (int, float))
    assert 0 <= score <= 100
    assert readiness.get("readiness_status") in {"READY", "CONDITIONAL", "WATCH", "BLOCKED"}
    assert readiness.get("status_rule") == "READY>=85; CONDITIONAL>=65; WATCH>=45; else BLOCKED"
    components = readiness.get("components", {})
    assert isinstance(components, dict)
    for key in [
        "owner_coverage_ratio",
        "blocker_map_coverage_ratio",
        "runtime_health_score",
        "artifact_growth_score",
        "blocker_pressure_score",
        "blocker_delta_bonus",
    ]:
        assert key in components
        assert isinstance(components[key], (int, float))


def test_governance_audit_packet_state_and_checklist_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "GOVERNANCE_AUDIT_PACKET_DECLARATION_v0: formal/docs/release/GOVERNANCE_AUDIT_PACKET_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_JSON_v0: formal/output/reports/governance_audit_packet_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_DIMENSION_RULE_v0: SEPARATE_ARTIFACT_GROWTH_EVIDENCE_GROWTH_AND_CLOSURE_GROWTH",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_LIFECYCLE_POLICY_DECLARATION_v0: formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_LIFECYCLE_POLICY_JSON_v0: formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_JSON_v0: formal/docs/release/GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_RUNTIME_BASELINE_DECLARATION_v0: formal/docs/release/GOVERNANCE_RUNTIME_BASELINE_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_RUNTIME_BASELINE_JSON_v0: formal/output/reports/governance_runtime_baseline_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_RUNTIME_CAPTURE_TOOL_v0: formal/python/tools/governance_runtime_baseline_capture.py",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_GROWTH_DECLARATION_v0: formal/docs/release/GOVERNANCE_ARTIFACT_GROWTH_BASELINE_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_GROWTH_BASELINE_JSON_v0: formal/output/reports/governance_artifact_growth_baseline_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_GROWTH_SNAPSHOT_JSON_v0: formal/output/reports/governance_artifact_growth_snapshot_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_GROWTH_SNAPSHOT_TOOL_v0: formal/python/tools/governance_artifact_growth_snapshot.py",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_CLOSURE_MAP_DECLARATION_v0: formal/docs/release/GOVERNANCE_BLOCKER_CLOSURE_MAP_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_CLOSURE_MAP_JSON_v0: formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_CLOSURE_MAP_TOOL_v0: formal/python/tools/governance_blocker_closure_map_generate.py",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_READINESS_DECLARATION_v0: formal/docs/release/GOVERNANCE_PROMOTION_READINESS_SCORE_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_READINESS_JSON_v0: formal/output/reports/governance_promotion_readiness_score_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_READINESS_TOOL_v0: formal/python/tools/governance_promotion_readiness_score.py",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_READINESS_STATUS_RULE_v0: READY_GE_85_CONDITIONAL_GE_65_WATCH_GE_45_ELSE_BLOCKED",
        "GOVERNANCE_AUDIT_PACKET_OWNER_COVERAGE_RULE_v0: EVERY_COMPLETION_ROW_REQUIRES_PRIMARY_AND_SECONDARY_OWNER_ASSIGNMENT",
        "GOVERNANCE_AUDIT_PACKET_GATE_v0: formal/python/tests/test_governance_audit_packet_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Governance audit packet pointer declared? YES / NO",
        "Governance runtime baseline recorded? YES / NO",
        "Branch-health runtime baseline recorded? YES / NO",
        "Artifact/evidence/closure dimensions separated? YES / NO",
        "Artifact lifecycle policy pointer declared? YES / NO",
        "Artifact family retention and archive thresholds pinned? YES / NO",
        "Closure owner map pointer declared? YES / NO",
        "Every closure row has primary and secondary owner? YES / NO",
        "Closure-growth delta recorded? YES / NO",
        "Blocker-to-closure map declaration pointer declared? YES / NO",
        "Blocker-to-closure map report pointer declared? YES / NO",
        "Blocker-to-closure map includes blocker class plus owning row/lane? YES / NO",
        "Blocker-to-closure map includes required closure artifact and exit criterion? YES / NO",
        "Promotion-readiness declaration pointer declared? YES / NO",
        "Promotion-readiness report pointer declared? YES / NO",
        "Promotion-readiness score recorded? YES / NO",
        "Promotion-readiness status recorded? YES / NO",
        "Promotion-readiness status rule applied? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"
