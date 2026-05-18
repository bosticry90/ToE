from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_006_audit_report import (
    AUDIT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AUDIT_COMMAND,
    LEAN_AXIOMS_USED,
    LEAN_IMPORT_MODULE,
    LEAN_SOURCE,
    LEAN_TARGET,
    NEXT_TARGET,
    OUTCOME_ID,
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
    TRANCHE_004_STATUS,
    TRANCHE_005_DEPENDENCY,
    TRANCHE_005_STATUS,
    TRANCHE_006_SOURCE_STATUS,
    build_audit,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
AUDIT_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_006_audit_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche006Audit.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "policy_adjudication_executed",
    "expert_re_review_executed",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "tranche_004_reclassified_nonblocking",
    "tranche_004_retained_blocker_discharged",
    "tranche_006_moved_or_cleared",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "release_readiness_pause_registered",
    "release_readiness_adjudication_prepared",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_dependency_remediation_tranche_006_audit_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert AUDIT_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_AUDIT_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_006_audit_consumes_result_review() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["schema_id"] == SCHEMA_ID
    assert audit["audit_id"] == AUDIT_ID
    assert audit["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert audit["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert audit["executed"] is True
    assert audit["accepted"] is True
    assert audit["outcome_id"] == OUTCOME_ID
    assert audit["consumes_tranche_006_execution_packet_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW_v0"
    )
    assert audit["consumes_tranche_006_execution_packet_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_006_audit_scope_is_single_dependency() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["audit_scope"] == (
        "EXECUTE_TRANCHE_006_LEAN_DEPENDENCY_AUDIT_ONLY_NO_REMEDIATION_OR_RELEASE_PROMOTION"
    )
    assert audit["tranche_001_status"] == TRANCHE_001_STATUS
    assert audit["tranche_002_status"] == TRANCHE_002_STATUS
    assert audit["tranche_003_status"] == TRANCHE_003_STATUS
    assert audit["tranche_005_status"] == TRANCHE_005_STATUS
    assert audit["tranche_005_dependency"] == TRANCHE_005_DEPENDENCY
    assert audit["tranche_004_status"] == TRANCHE_004_STATUS
    assert audit["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert audit["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert audit["selected_dependency"] == SELECTED_DEPENDENCY
    assert audit["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert audit["selected_obligation_status_after_audit"] == (
        "release_blocking_pending_tranche_006_audit_result_review"
    )
    assert audit["audit_status"] == "executed_evidence_captured"
    assert audit["evidence_surface_exists"] is True


def test_v01_alpha_dependency_remediation_tranche_006_audit_carries_tranche_004() -> None:
    audit = _json(AUDIT_PATH)
    retained = audit["retained_tranche_004_carry_forward"]
    assert retained["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert retained["dependency"] == TRANCHE_004_DEPENDENCY
    assert retained["status"] == TRANCHE_004_STATUS
    assert retained["current_blocker"] == TRANCHE_004_CURRENT_BLOCKER
    assert retained["moved_to_documented_dependency_nonblocking"] is False
    assert audit["release_readiness_blocked_by_tranche_004"] is True
    assert audit["global_release_readiness_still_blocked"] is True


def test_v01_alpha_dependency_remediation_tranche_006_audit_captures_exact_lean_evidence() -> None:
    audit = _json(AUDIT_PATH)
    evidence = audit["lean_evidence"]
    assert evidence["lean_target"] == LEAN_TARGET
    assert evidence["lean_source"] == LEAN_SOURCE
    assert evidence["lean_import_module"] == LEAN_IMPORT_MODULE
    assert evidence["command"] == LEAN_AUDIT_COMMAND
    assert evidence["command_context"] == "lake env lean --stdin"
    assert evidence["stdin_script"] == (
        "import ToeFormal.Bridges.SR_CosmologyRegimeTransport\n"
        "#print axioms ToeFormal.Bridges.SRCosmologyRegimeTransport."
        "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0\n"
    )
    assert evidence["exit_code"] == 0
    assert evidence["raw_output"] == (
        "'ToeFormal.Bridges.SRCosmologyRegimeTransport."
        "supplied_alignment_constructs_sr_cosmo_regime_transport_package_v0' depends on axioms: "
        "[propext,\n Classical.choice,\n Quot.sound]"
    )
    assert evidence["parsed_axioms"] == LEAN_AXIOMS_USED
    assert evidence["exact_axioms_or_dependencies_used"] == LEAN_AXIOMS_USED
    assert audit["lean_dependency_audit_executed"] is True
    assert audit["lean_dependency_evidence_captured"] is True


def test_v01_alpha_dependency_remediation_tranche_006_audit_classifies_project_axioms_separately() -> None:
    audit = _json(AUDIT_PATH)
    evidence = audit["lean_evidence"]
    assert evidence["standard_lean_axioms_used"] == LEAN_AXIOMS_USED
    assert evidence["standard_lean_or_mathlib_axioms_used"] == LEAN_AXIOMS_USED
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["project_local_axioms_present"] is False
    assert evidence["depends_only_on_standard_lean_or_mathlib_axioms"] is True
    assert evidence["axiom_classification"] == [
        {"axiom": "propext", "classification": "standard_lean_axiom"},
        {"axiom": "Classical.choice", "classification": "standard_lean_axiom"},
        {"axiom": "Quot.sound", "classification": "standard_lean_axiom"},
    ]
    assert evidence["classification"] == (
        "exact_dependency_evidence_produced_no_project_axioms_detected"
    )
    assert evidence["theorem_debt_discharged_by_this_audit"] is False
    assert evidence["proof_debt_reduced_by_this_audit"] is False
    assert evidence["retained_assumptions_discharged_by_this_audit"] is False


def test_v01_alpha_dependency_remediation_tranche_006_audit_evidence_surfaces() -> None:
    audit = _json(AUDIT_PATH)
    surfaces = audit["evidence_surfaces_produced_or_updated"]
    assert {row["kind"]: row["status"] for row in surfaces} == {
        "tranche_006_audit_result_packet": "produced",
        "lean_axiom_print_output": "produced",
    }
    assert audit["lean_surfaces_touched"] == [
        {
            "surface": LEAN_SOURCE,
            "touch_kind": "read_and_axiom_print_only",
            "modified": False,
        }
    ]
    assert audit["documentation_surfaces_touched"] == []


def test_v01_alpha_dependency_remediation_tranche_006_audit_carries_forward_current_blockers() -> None:
    audit = _json(AUDIT_PATH)
    rows = audit["remaining_release_blocking_obligations"]
    assert audit["remaining_release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in rows] == [
        TRANCHE_004_FINDING_ID,
        SELECTED_FINDING_ID,
    ]
    assert rows[0]["status_carry_forward"] == TRANCHE_004_STATUS
    assert rows[1]["status_carry_forward"] == TRANCHE_006_SOURCE_STATUS

    other = audit["other_release_blocking_obligations"]
    assert audit["other_release_blocking_obligation_count"] == 1
    assert other[0]["dependency_finding_id"] == TRANCHE_004_FINDING_ID
    assert other[0]["status_carry_forward"] == TRANCHE_004_STATUS
    assert other[0]["modified_by_tranche_006"] is False


def test_v01_alpha_dependency_remediation_tranche_006_audit_no_broader_remediation_or_movement() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["tranche_006_audit_result_classification"] == (
        "lean_dependency_audit_evidence_captured_pending_result_review"
    )
    assert audit["remediation_executed"] is False
    assert audit["broader_remediation_executed"] is False
    assert audit["blocker_movement_registered"] is False
    assert audit["blocker_movement_authorized"] is False
    assert audit["blocker_fully_remediated"] is False
    assert audit["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert audit["tranche_004_retained_blocker_discharged"] is False
    assert audit["tranche_006_moved_or_cleared"] is False


def test_v01_alpha_dependency_remediation_tranche_006_audit_forbidden_effects_false() -> None:
    audit = _json(AUDIT_PATH)
    forbidden = audit["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert audit["release_packet_assembled"] is False
    assert audit["v01_alpha_marked_ready"] is False
    assert audit["release_readiness_pause_registered"] is False
    assert audit["release_readiness_adjudication_prepared"] is False
    assert audit["lean_theorem_debt_discharged"] is False
    assert audit["axiom_spec_backed_debt_reduced"] is False
    assert audit["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert audit["proof_debt_reduced"] is False
    assert audit["retained_assumptions_discharged"] is False
    assert audit["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_tranche_006_audit_next_target() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["post_audit_adjudication_target"] == NEXT_TARGET
    assert audit["selected_next_target"] == NEXT_TARGET
    assert audit["selected_next_target_kind"] == "tranche_006_audit_result_review_only"
    assert audit["selection_count"] == 1
    assert audit["next_action_scope"] == (
        "REVIEW_TRANCHE_006_LEAN_AUDIT_EVIDENCE_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in audit["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_006_audit_result": "selected",
        "prepare_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet": "deferred",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_006_audit_acceptance_and_determinism() -> None:
    audit = _json(AUDIT_PATH)
    for key, value in audit["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_audit(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_audit(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert audit == generated_1


def test_v01_alpha_dependency_remediation_tranche_006_audit_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        AUDIT_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_006_AUDIT_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_006_audit_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_006_audit_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_AUDIT_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche006Audit" in index_text
    assert "v01_dependency_remediation_tranche_006_audit_does_not_move_blocker" in index_text
