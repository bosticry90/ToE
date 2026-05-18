from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_002_audit_report import (
    AUDIT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AUDIT_COMMAND,
    LEAN_AXIOMS_USED,
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
    build_audit,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
AUDIT_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_002_audit_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche002Audit.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "expert_re_review_executed",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
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

RELEASE_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-002",
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

OTHER_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-003",
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

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


def test_v01_alpha_dependency_remediation_tranche_002_audit_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert AUDIT_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_AUDIT_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_002_audit_consumes_result_review() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["schema_id"] == SCHEMA_ID
    assert audit["audit_id"] == AUDIT_ID
    assert audit["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert audit["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert audit["executed"] is True
    assert audit["accepted"] is True
    assert audit["outcome_id"] == OUTCOME_ID
    assert audit["consumes_tranche_002_execution_packet_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_v0"
    )
    assert audit["consumes_tranche_002_execution_packet_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_002_audit_scope_is_single_dependency() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["audit_scope"] == (
        "EXECUTE_TRANCHE_002_LEAN_DEPENDENCY_AUDIT_ONLY_NO_REMEDIATION_OR_RELEASE_PROMOTION"
    )
    assert audit["tranche_001_status"] == TRANCHE_001_STATUS
    assert audit["tranche_001_global_release_readiness_still_not_marked"] is True
    assert audit["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert audit["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert audit["selected_dependency"] == SELECTED_DEPENDENCY
    assert audit["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert audit["selected_obligation_status_after_audit"] == (
        "release_blocking_pending_tranche_002_audit_result_review"
    )
    assert audit["audit_status"] == "executed_evidence_captured"
    assert audit["evidence_surface_exists"] is True


def test_v01_alpha_dependency_remediation_tranche_002_audit_captures_exact_lean_evidence() -> None:
    audit = _json(AUDIT_PATH)
    evidence = audit["lean_evidence"]
    assert evidence["lean_target"] == LEAN_TARGET
    assert evidence["lean_source"] == LEAN_SOURCE
    assert evidence["command"] == LEAN_AUDIT_COMMAND
    assert evidence["command_context"] == "lake env lean --stdin"
    assert evidence["stdin_script"] == (
        "import ToeFormal.QFT.FreeScalarDerivation\n"
        "#print axioms ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero\n"
    )
    assert evidence["exit_code"] == 0
    assert evidence["raw_output"] == (
        "'ToeFormal.QFT.FreeScalarDerivation.stationary_implies_operator_zero' "
        "depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"
    )
    assert evidence["parsed_axioms"] == LEAN_AXIOMS_USED
    assert evidence["exact_axioms_or_dependencies_used"] == LEAN_AXIOMS_USED
    assert audit["lean_dependency_audit_executed"] is True
    assert audit["lean_dependency_evidence_captured"] is True


def test_v01_alpha_dependency_remediation_tranche_002_audit_classifies_project_axioms_separately() -> None:
    audit = _json(AUDIT_PATH)
    evidence = audit["lean_evidence"]
    assert evidence["standard_lean_axioms_used"] == LEAN_AXIOMS_USED
    assert evidence["standard_lean_axiom_count"] == 3
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
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


def test_v01_alpha_dependency_remediation_tranche_002_audit_evidence_surfaces() -> None:
    audit = _json(AUDIT_PATH)
    surfaces = audit["evidence_surfaces_produced_or_updated"]
    assert {row["kind"]: row["status"] for row in surfaces} == {
        "tranche_002_audit_result_packet": "produced",
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


def test_v01_alpha_dependency_remediation_tranche_002_audit_carries_forward_blockers() -> None:
    audit = _json(AUDIT_PATH)
    rows = audit["release_blocking_obligations_carry_forward"]
    assert audit["release_blocking_obligation_count"] == 5
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS

    other = audit["other_release_blocking_obligations"]
    assert audit["other_release_blocking_obligation_count"] == 4
    assert [row["dependency_finding_id"] for row in other] == OTHER_BLOCKER_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_002"
        assert row["remediation_execution_status"] == "not_executed_v0"
        assert row["modified_by_tranche_002"] is False


def test_v01_alpha_dependency_remediation_tranche_002_audit_no_broader_remediation_or_movement() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["tranche_002_audit_result_classification"] == (
        "lean_dependency_audit_evidence_captured_pending_result_review"
    )
    assert audit["remediation_executed"] is False
    assert audit["broader_remediation_executed"] is False
    assert audit["blocker_movement_registered"] is False
    assert audit["blocker_movement_authorized"] is False
    assert audit["blocker_fully_remediated"] is False


def test_v01_alpha_dependency_remediation_tranche_002_audit_forbidden_effects_false() -> None:
    audit = _json(AUDIT_PATH)
    forbidden = audit["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert audit["release_packet_assembled"] is False
    assert audit["v01_alpha_marked_ready"] is False
    assert audit["lean_theorem_debt_discharged"] is False
    assert audit["axiom_spec_backed_debt_reduced"] is False
    assert audit["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert audit["proof_debt_reduced"] is False
    assert audit["retained_assumptions_discharged"] is False
    assert audit["validation_claim_authorized"] is False

    combined = json.dumps(audit, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_dependency_remediation_tranche_002_audit_next_target() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["post_audit_adjudication_target"] == NEXT_TARGET
    assert audit["selected_next_target"] == NEXT_TARGET
    assert audit["selected_next_target_kind"] == "tranche_002_audit_result_review_only"
    assert audit["selection_count"] == 1
    assert audit["next_action_scope"] == (
        "REVIEW_TRANCHE_002_LEAN_AUDIT_EVIDENCE_ONLY_NO_REMEDIATION_CLOSURE_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in audit["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_002_audit_result": "selected",
        "execute_v01_alpha_dependency_remediation_tranche_002_policy_adjudication": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_002_audit_acceptance_and_determinism() -> None:
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


def test_v01_alpha_dependency_remediation_tranche_002_audit_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        AUDIT_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_002_AUDIT_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_002_audit_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_002_audit_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_AUDIT_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche002Audit" in index_text
    assert "v01_dependency_remediation_tranche_002_audit_does_not_move_blocker" in index_text
