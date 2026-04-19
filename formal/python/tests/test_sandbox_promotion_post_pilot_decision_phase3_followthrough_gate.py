from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PHASE3_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_MIGRATION_PHASE3_AUTHORITY_OWNERSHIP_HARDENING_DECLARATION_20260419_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json"


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "governed_review_report": "formal/output/reports/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json",
                "governed_review_wrapper": "formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json",
                "pilot_binding": "formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
                "phase2_phase6_declaration": "formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE6_DECLARATION_20260419_v0.md",
            },
            "candidate_routes": [
                {"route_id": "HOLD_NONWIDENED_ROUTE", "next_action": "IMPLEMENT_AUTHORITY_OWNERSHIP_HARDENING_TRANCHE_BEFORE_ANY_WIDENING_OR_RETIREMENT"},
                {"route_id": "WIDEN_PROMOTION_ROUTE", "next_action": "DECLARE_NEXT_BOUNDED_PROMOTION_WIDENING_TRANCHE"},
                {"route_id": "RETIRE_TO_SANDBOX_ONLY_ROUTE", "next_action": "RETURN_PILOT_TO_SANDBOX_ONLY_STATUS_AND_DECLARE_RETIREMENT_REVIEW_IF_NEEDED"},
            ],
            "decision_policy": {
                "required_hold_decision": "hold",
                "required_hold_terminal_outcome": "SANDBOX_PROMOTION_GOVERNED_REVIEW_HOLD_DECISION_EMITTED",
                "required_artifact_adjudication_for_nonwidened_hold": "NOT_YET_DISCHARGED",
                "no_loop_rule": "ONE_SANDBOX_PROMOTION_POST_PILOT_DECISION_ONLY",
                "no_further_widening_policy": "NO_WIDENING_OR_RETIREMENT_BEFORE_POST_PILOT_DECISION_IS_FORMALIZED",
            },
        },
    )


def _seed_inputs(root: Path, *, terminal_outcome: str = "SANDBOX_PROMOTION_GOVERNED_REVIEW_HOLD_DECISION_EMITTED", decision: str = "hold", adjudication: str = "NOT_YET_DISCHARGED", mutation_emitted: bool = False) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json",
        {
            "schema_id": "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_REPORT_20260419_v0",
            "summary": {
                "terminal_outcome": terminal_outcome,
                "governed_decision": decision,
                "canonical_mutation_emitted": mutation_emitted,
                "artifact_adjudication": adjudication,
            },
            "objective_quality": {
                "summary": {
                    "next_action": "REPAIR_OR_EXTEND_COSMO_SR_SANDBOX_EVIDENCE_BEFORE_ANY_CANONICAL_MUTATION"
                }
            },
        },
    )
    _write_json(
        root / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json",
        {"schema_id": "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0"},
    )
    _write_json(
        root / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
        {"pilot_binding": {"pilot_track_id": "SANDBOX_PROMOTION_PILOT_COSMO_SR_CYCLE07", "target_row_id": "ROW-SEAM-COSMO-SR-001", "target_seam_id": "SEAM-COSMO-SR"}},
    )
    _write_text(
        root / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE6_DECLARATION_20260419_v0.md",
        "Phase 2 completion and Phase 6 bounded audit kickoff\n",
    )


def test_post_pilot_decision_holds_nonwidened_and_routes_to_phase3(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_POST_PILOT_DECISION_COSMO_SR_CYCLE07_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["post_pilot_decision"] == "RETAIN_BOUNDED_PILOT_NONWIDENED_AFTER_GOVERNED_HOLD"
    assert report["summary"]["pilot_disposition"] == "HOLD_NONWIDENED"
    assert report["summary"]["next_action"] == "IMPLEMENT_AUTHORITY_OWNERSHIP_HARDENING_TRANCHE_BEFORE_ANY_WIDENING_OR_RETIREMENT"


def test_post_pilot_decision_widen_candidate_when_governed_promote_exists(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_POST_PILOT_DECISION_COSMO_SR_CYCLE07_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, terminal_outcome="SANDBOX_PROMOTION_GOVERNED_REVIEW_PROMOTE_DECISION_EMITTED", decision="promote", adjudication="DISCHARGED", mutation_emitted=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["post_pilot_decision"] == "AUTHORIZE_NEXT_BOUNDED_PROMOTION_WIDENING_REVIEW"


def test_phase3_declaration_structure_and_live_surface_refs() -> None:
    text = _read(PHASE3_DECLARATION_PATH)
    for section in (
        "## Tranche name",
        "## Objective",
        "## Allowed files",
        "## Out of scope",
        "## Acceptance",
        "## Rollback anchor",
        "## Hard stop rule",
        "## Boundary freshness note",
    ):
        assert section in text

    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    for token in (
        "SANDBOX_PROMOTION_POST_PILOT_DECISION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_POST_PILOT_DECISION_COSMO_SR_CYCLE07_20260419_v0.json",
        "SANDBOX_PROMOTION_POST_PILOT_DECISION_REPORT_v0: formal/output/reports/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json",
        "SANDBOX_PROMOTION_POST_PILOT_DECISION_TOOL_v0: formal/python/tools/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_report.py",
        "SANDBOX_PROMOTION_PHASE7_PHASE3_GATE_v0: formal/python/tests/test_sandbox_promotion_post_pilot_decision_phase3_followthrough_gate.py",
        "SANDBOX_PROMOTION_MIGRATION_PHASE3_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_AUTHORITY_OWNERSHIP_HARDENING_DECLARATION_20260419_v0.md",
        "SANDBOX_PROMOTION_PHASE3_IMPLEMENTATION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_IMPLEMENTATION_20260419_v0.md",
        "SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
        "SANDBOX_PROMOTION_AUTHORITY_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
        "SANDBOX_PROMOTION_PHASE5_IMPLEMENTATION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE5_IMPLEMENTATION_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
        "SANDBOX_PROMOTION_PHASE5_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
        "SANDBOX_PROMOTION_MIGRATION_PHASE3_STATUS_v0: OBJECTIVELY_COMPLETE_AUTHORITY_OWNER_MATRIX_AND_FAIL_CLOSED_CUTOVER_GATE_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE5_STATUS_v0: OBJECTIVELY_COMPLETE_BOUNDARY_ENFORCEMENT_FAMILY_AND_FAIL_CLOSED_CLOSEOUT_GATE_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE7_STATUS_v0: OBJECTIVELY_COMPLETE_POST_PILOT_DECISION_PINNED_NONWIDENED_AFTER_GOVERNED_HOLD",
        "SANDBOX_PROMOTION_ARCHITECTURE_NEXT_ACTION_v0: ROUTE_FUTURE_BOUNDED_WORK_THROUGH_COMPLETED_SANDBOX_PROMOTION_GOVERNANCE_STACK",
    ):
        assert token in state_text
        assert token in roadmap_text

    report = _read_json(REPORT_PATH)
    assert report["summary"]["post_pilot_decision"] == "RETAIN_BOUNDED_PILOT_NONWIDENED_AFTER_GOVERNED_HOLD"