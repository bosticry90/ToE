from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.computational_physics_capability_audit_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_20260515_v0.json"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "computational_physics_capability_audit_result_review_report.py"
)

FORBIDDEN_TRUE_KEYS = [
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "phase2_authorization",
    "empirical_validation_claim",
    "seam_closure",
    "master_action_promotion",
    "external_truth_claim",
]

PROHIBITED_PHRASES = [
    "Phase 2 authorized",
    "seam closure authorized",
    "empirical validation complete",
    "master action promoted",
    "theorem discharged by computation",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _payload() -> dict:
    return json.loads(_read(REVIEW_PATH))


def test_capability_audit_result_review_files_exist() -> None:
    assert AUDIT_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_capability_audit_result_review_consumes_audit_and_accepts_nonclaim_result() -> None:
    payload = _payload()
    assert payload["schema_id"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_20260515_v0"
    assert payload["review_id"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_v0"
    assert payload["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert payload["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert payload["consumed_audit"]["audit_id"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
    assert payload["consumed_audit"]["audit_path"] == (
        "formal/docs/release/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
    )
    assert payload["consumed_audit"]["audit_row_count"] == 8
    assert payload["accepted"] is True
    assert payload["outcome_id"] == OUTCOME_ID


def test_capability_audit_result_review_enforces_acceptance_criteria() -> None:
    payload = _payload()
    criteria = payload["acceptance_criteria"]
    for key, value in criteria.items():
        assert value is True, f"Acceptance criterion failed: {key}"

    scope = payload["scope_confirmation"]
    assert scope["promotion_allowed_count"] == 0
    assert scope["missing_evidence_count"] == 0
    assert scope["archive_or_quarantine_path_count"] == 0
    assert scope["archive_or_quarantine_paths"] == []
    assert scope["whole_repo_inventory_claimed"] is False
    assert scope["every_python_test_inventory_claimed"] is False
    assert scope["every_lean_file_inventory_claimed"] is False


def test_capability_audit_result_review_forbidden_effects_are_all_false() -> None:
    payload = _payload()
    forbidden = payload["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(payload, sort_keys=True) + "\n" + _read(ROADMAP_PATH) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_capability_audit_result_review_authorizes_vvuq_preparation_only() -> None:
    payload = _payload()
    assert payload["next_packet"] == "VVUQ_CREDIBILITY_LEDGER_v0"
    assert payload["next_action"] == "PREPARE_VVUQ_CREDIBILITY_LEDGER_AFTER_CAPABILITY_AUDIT_REVIEW"
    assert payload["next_packet_authorization_scope"] == "PREPARATION_ONLY"
    assert payload["gap_readout"]["strongest_gap_pattern"] == (
        "UQ_DEPTH_AND_VALIDATION_DEPTH_ARE_PRIMARY_NEXT_CREDIBILITY_GAPS"
    )


def test_capability_audit_result_review_report_is_deterministic() -> None:
    generated_1 = build_result_review(audit_path=AUDIT_PATH, captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    generated_2 = build_result_review(audit_path=AUDIT_PATH, captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    assert generated_1 == generated_2
    assert _payload() == generated_1


def test_capability_audit_result_review_is_pinned_and_next_action_is_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: REVIEW_VVUQ_CREDIBILITY_LEDGER_RESULT" not in roadmap_text
    assert "CREATE_COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_PACKET" not in roadmap_text
    assert "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_OUTCOME_v0: "
        "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_ACCEPTS_BOUNDED_NONCLAIM_CLASSIFICATION_"
        "AND_AUTHORIZES_VVUQ_LEDGER_PREPARATION_ONLY"
    ) in roadmap_text

    for ref in (
        "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_v0",
        "formal/docs/release/COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/computational_physics_capability_audit_result_review_report.py",
        "formal/python/tests/test_computational_physics_capability_audit_result_review_gate.py",
    ):
        assert ref in physics_text
