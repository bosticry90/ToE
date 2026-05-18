from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_001_execution_report import (
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AXIOMS_USED,
    NEXT_TARGET,
    OUTCOME_ID,
    SELECTED_DEPENDENCY,
    SELECTED_REMEDIATION_FINDING_ID,
    SELECTED_TRANCHE_ID,
    build_execution,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
EXECUTION_PATH = (
    RELEASE_DIR / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_001_execution_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche001Execution.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

CLOSED_EFFECT_KEYS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "blocker_movement_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]

OTHER_EXPECTED_IDS = [
    "V01-ALPHA-DEP-REM-002",
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


def test_v01_alpha_dependency_remediation_tranche_001_execution_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert EXECUTION_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_EXECUTION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_001_execution_consumes_result_review() -> None:
    execution = _json(EXECUTION_PATH)
    assert execution["schema_id"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_20260515_v0"
    )
    assert execution["execution_id"] == "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_v0"
    assert execution["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert execution["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert execution["executed"] is True
    assert execution["accepted"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert execution["consumes_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_v0"
    )
    assert execution["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_001_execution_scope_is_single_dependency() -> None:
    execution = _json(EXECUTION_PATH)
    assert execution["execution_scope"] == (
        "EXECUTE_DEPENDENCY_REMEDIATION_TRANCHE_001_ONLY_NO_RELEASE_PROMOTION"
    )
    assert execution["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert execution["selected_remediation_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert execution["selected_dependency"] == SELECTED_DEPENDENCY
    assert execution["selected_dependency_qualified_name"] == (
        "ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg"
    )
    selected = execution["selected_dependency_execution"]
    assert selected["dependency_finding_id"] == SELECTED_REMEDIATION_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY
    assert selected["execution_result"] == "succeeded_evidence_produced"
    assert selected["remediation_status_after_execution"] == (
        "pending_result_review_no_blocker_movement_claim"
    )
    assert selected["blocker_resolution_claim"] is False
    assert selected["expert_re_review_required"] is True
    assert selected["result_review_required"] is True


def test_v01_alpha_dependency_remediation_tranche_001_execution_produces_lean_evidence() -> None:
    execution = _json(EXECUTION_PATH)
    evidence = execution["lean_evidence"]
    assert evidence["command"] == (
        "#print axioms ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg"
    )
    assert evidence["command_context"] == "lake env lean --stdin"
    assert evidence["exit_code"] == 0
    assert evidence["parsed_axioms"] == LEAN_AXIOMS_USED
    assert evidence["project_axioms_used"] == []
    assert evidence["project_axiom_count"] == 0
    assert evidence["classification"] == (
        "exact_dependency_evidence_produced_no_project_axioms_detected"
    )
    assert evidence["theorem_debt_discharged_by_this_execution"] is False
    assert evidence["proof_debt_reduced_by_this_execution"] is False
    assert evidence["retained_assumptions_discharged_by_this_execution"] is False

    surfaces = execution["evidence_surfaces_produced_or_updated"]
    assert {row["kind"]: row["status"] for row in surfaces} == {
        "tranche_execution_result_packet": "produced",
        "lean_axiom_print_output": "produced",
    }
    assert execution["lean_surfaces_touched"] == [
        {
            "surface": "formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean",
            "touch_kind": "read_and_axiom_print_only",
            "modified": False,
        }
    ]
    assert execution["documentation_surfaces_touched"] == []


def test_v01_alpha_dependency_remediation_tranche_001_execution_carries_forward_other_five() -> None:
    execution = _json(EXECUTION_PATH)
    other = execution["other_release_blocking_obligations"]
    assert execution["other_release_blocking_obligation_count"] == 5
    assert [row["dependency_finding_id"] for row in other] == OTHER_EXPECTED_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_executed_in_tranche_001"
        assert row["remediation_execution_status"] == "not_executed_v0"
        assert row["modified_by_tranche_001"] is False


def test_v01_alpha_dependency_remediation_tranche_001_execution_closed_effects_false() -> None:
    execution = _json(EXECUTION_PATH)
    closed = execution["closed_effect_status"]
    assert sorted(closed) == sorted(CLOSED_EFFECT_KEYS)
    for key in CLOSED_EFFECT_KEYS:
        assert closed[key] is False

    assert execution["release_packet_assembled"] is False
    assert execution["v01_alpha_marked_ready"] is False
    assert execution["lean_theorem_debt_discharged"] is False
    assert execution["axiom_spec_backed_debt_reduced"] is False
    assert execution["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert execution["proof_debt_reduced"] is False
    assert execution["retained_assumptions_discharged"] is False
    assert execution["validation_claim_authorized"] is False

    combined = json.dumps(execution, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_dependency_remediation_tranche_001_execution_next_target() -> None:
    execution = _json(EXECUTION_PATH)
    assert execution["post_execution_adjudication_target"] == NEXT_TARGET
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == "tranche_execution_result_review_only"
    assert execution["selection_count"] == 1
    assert execution["next_action_scope"] == (
        "REVIEW_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_ONLY_NO_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in execution["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_001_execution_result": "selected",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
        "execute_v01_alpha_dependency_remediation_tranche_002": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_001_execution_acceptance_and_determinism() -> None:
    execution = _json(EXECUTION_PATH)
    for key, value in execution["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_execution(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_execution(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert execution == generated_1


def test_v01_alpha_dependency_remediation_tranche_001_execution_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_v0",
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_001_execution_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_001_execution_gate.py",
        OUTCOME_ID,
        "review_v01_alpha_dependency_remediation_tranche_001_execution_result",
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_EXECUTION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche001Execution" in index_text
    assert "v01_dependency_remediation_tranche_001_execution_does_not_promote_release" in index_text
