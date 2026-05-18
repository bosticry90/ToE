from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXPECTED_AXIOMS,
    FORBIDDEN_EFFECTS,
    LEAN_AUDIT_COMMAND,
    LEAN_SOURCE,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    PROJECT_AXIOMS_USED,
    SCHEMA_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_005_DEPENDENCY,
    TRANCHE_005_STATUS,
    build_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_20260515_v0.json"
)
PACKET_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche006ReleasePolicyAdjudicationPacket.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

PROHIBITED_POSITIVE_PHRASES = [
    "release packet assembled true",
    "v0.1-alpha marked ready",
    "Lean theorem debt discharged true",
    "proof debt reduced true",
    "retained assumptions discharged true",
    "Phase 2 authorized true",
    "seam closure authorized true",
    "empirical validation authorized true",
    "master action promoted",
    "claim promoted",
    "release packet ready",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert PACKET_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_consumes_result_review() -> None:
    packet = _json(PACKET_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_audit_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_v0"
    )
    assert packet["consumes_audit_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_RESULT_REVIEW_20260515_v0.json"
    )
    assert packet["source_audit"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_v0"


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_preserves_selected_dependency() -> None:
    packet = _json(PACKET_PATH)
    assert packet["packet_scope"] == (
        "PREPARE_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_NO_POLICY_DECISION_OR_RELEASE_PROMOTION"
    )
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_005_status"] == TRANCHE_005_STATUS
    assert packet["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert packet["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert packet["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert packet["selected_dependency"] == SELECTED_DEPENDENCY
    assert packet["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    selected = packet["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_preserves_evidence() -> None:
    packet = _json(PACKET_PATH)
    assert packet["lean_audit_target"]["lean_target"] == LEAN_TARGET
    assert packet["lean_audit_target"]["lean_source"] == LEAN_SOURCE
    assert packet["lean_audit_target"]["command"] == LEAN_AUDIT_COMMAND
    assert packet["lean_audit_target"]["exit_code"] == 0

    evidence = packet["accepted_lean_dependency_evidence"]
    assert evidence["parsed_axioms"] == EXPECTED_AXIOMS
    assert evidence["exact_axioms_or_dependencies_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_or_mathlib_axioms_used"] == EXPECTED_AXIOMS
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["project_local_axioms_present"] is False
    assert evidence["classification"] == "exact_dependency_evidence_produced_no_project_axioms_detected"
    assert SELECTED_DEPENDENCY in evidence["raw_output"]


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_defines_policy_question_without_deciding() -> None:
    packet = _json(PACKET_PATH)
    assert packet["policy_question"] == (
        "Are [propext, Classical.choice, Quot.sound] acceptable standard Lean dependencies "
        "for tranche 006 / supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0 "
        "under the v0.1-alpha release dependency policy, given project_axioms_used = []?"
    )
    assert len(packet["release_policy_acceptance_criteria"]) >= 6
    assert len(packet["release_policy_failure_criteria"]) >= 6
    assert "standard Lean axiom posture of tranche 006" in packet["expert_re_review_requirement"]
    assert packet["policy_decision_made"] is False
    assert packet["policy_adjudication_executed"] is False
    assert packet["release_policy_adjudication_executed"] is False
    assert packet["release_policy_adjudication_prepared"] is True
    assert packet["blocker_downgrade_allowed_by_this_packet"] is False
    assert packet["blocker_may_be_downgraded_after_adjudication"] == (
        "only_if_later_policy_adjudication_accepts_standard_lean_axiom_posture"
    )


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_carries_tranche_004() -> None:
    packet = _json(PACKET_PATH)
    assert packet["tranche_004_status"] == TRANCHE_004_STATUS
    retained = packet["retained_tranche_004_carry_forward"]
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["retained_blocker_reason"] == TRANCHE_004_RETAINED_REASON
    assert packet["release_readiness_blocked_by_tranche_004"] is True
    assert packet["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert packet["tranche_004_retained_blocker_discharged"] is False


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_keeps_blockers_tracked() -> None:
    packet = _json(PACKET_PATH)
    assert packet["tranche_006_release_blocker_status"] == (
        "still_blocking_pending_release_policy_adjudication_packet_result_review"
    )
    assert packet["remediation_closure_authorized"] is False
    assert packet["remediation_closure_executed"] is False
    assert packet["remediation_fully_satisfied"] is False
    assert packet["blocker_movement_authorized"] is False
    assert packet["blocker_movement_registered"] is False
    assert packet["tranche_006_moved_or_cleared"] is False

    rows = packet["release_blocking_obligations_carry_forward"]
    assert packet["release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in rows] == [
        TRANCHE_004_FINDING_ID,
        SELECTED_FINDING_ID,
    ]
    assert rows[0]["status_carry_forward"] == TRANCHE_004_STATUS
    assert rows[0]["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert rows[1]["status_carry_forward"] == (
        "release_blocking_pending_tranche_006_release_policy_adjudication_packet_result_review"
    )
    for row in rows:
        assert row["modified_by_tranche_006_release_policy_packet"] is False

    other = packet["other_release_blocking_obligations"]
    assert packet["other_release_blocking_obligation_count"] == 1
    assert other[0]["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert other[0]["status_carry_forward"] == TRANCHE_004_STATUS
    assert other[0]["modified_by_tranche_006_release_policy_packet"] is False


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_forbidden_effects_false() -> None:
    packet = _json(PACKET_PATH)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["validation_claim_authorized"] is False

    combined = json.dumps(packet, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_next_target() -> None:
    packet = _json(PACKET_PATH)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "release_policy_adjudication_packet_result_review_only"
    )
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "REVIEW_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_ONLY_NO_POLICY_DECISION"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication": "deferred",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_acceptance_and_determinism() -> None:
    packet = _json(PACKET_PATH)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_RELEASE_POLICY_ADJUDICATION_PACKET_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche006ReleasePolicyAdjudicationPacket" in index_text
    assert (
        "v01_dependency_remediation_tranche_006_release_policy_adjudication_packet_does_not_make_policy_decision"
        in index_text
    )
