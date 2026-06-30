from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_report import (
    DEFAULT_OUT as ATTEMPT_OUT,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    STRICT_ATTEMPT_PREPARATION_RESULT,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    DEFAULT_OUT,
    EXECUTION_ROUTE_TO_AUTHORIZE,
    FIELD_EULER_LAGRANGE_EQUATION,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_CONDITION,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PREPARED_LINKAGE_TARGET,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_PURITY_WATCH_ITEMS,
    SCHEMA_ID,
    STANDALONE_PHI_SOURCE_ROUTE,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET_CONCLUSION,
    build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
CURRENT_TARGET_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CurrentTarget.lean"
)
QFTGR_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_AUTHORITY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def consumed_target() -> str:
    return "review_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result"


def attempt_target() -> str:
    return "prepare_phi_source_theorem_linkage_attempt_from_standalone_phi_route"


def test_phi_source_standalone_attempt_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_source_standalone_attempt_result_review_accepts_preparation() -> None:
    review = _json(DEFAULT_OUT)

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["reviewed"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == OUTCOME_ID
    assert review["packet_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == consumed_target()
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["suggested_execution_outcome"] == SUGGESTED_EXECUTION_OUTCOME
    assert review["strict_suggested_execution_outcome"] == (
        STRICT_SUGGESTED_EXECUTION_OUTCOME
    )
    assert review["attempt_preparation_result"] == ATTEMPT_OUTCOME
    assert review["attempt_strict_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review() == review


def test_phi_source_standalone_attempt_result_review_preserves_phi_route() -> None:
    review = _json(DEFAULT_OUT)

    assert review["standalone_phi_source_route"] == STANDALONE_PHI_SOURCE_ROUTE
    assert review["standalone_phi_source_route_preserved"] is True
    assert review["C_source_phi_residual_definition"] == C_SOURCE_PHI_RESIDUAL_DEFINITION
    assert review["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert review["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert review["on_shell_condition"] == ON_SHELL_CONDITION
    assert review["field_euler_lagrange_equation"] == FIELD_EULER_LAGRANGE_EQUATION
    assert review["target_conclusion"] == TARGET_CONCLUSION
    assert review["prepared_linkage_target"] == PREPARED_LINKAGE_TARGET
    assert review["execution_route_to_authorize"] == EXECUTION_ROUTE_TO_AUTHORIZE
    assert review["plain_meaning"] == PLAIN_MEANING
    assert review["route_kind"] == "standalone_phi_on_shell_scalar_residual"


def test_phi_source_standalone_attempt_result_review_preserves_boundaries() -> None:
    review = _json(DEFAULT_OUT)
    route_text = " ".join(review["execution_route_to_authorize"])

    assert review["route_purity_watch_items"] == ROUTE_PURITY_WATCH_ITEMS
    assert "J^alpha" not in route_text
    assert "nabla_mu F" not in route_text
    assert "QFT-GR" not in route_text
    assert review["old_omnibus_tests_historical_hard_coded"] is True
    assert review["old_omnibus_tests_not_active_acceptance_authority"] is True

    for flag in [
        "review_executes_theorem",
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_execution_authorized",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_source_phi_discharged",
        "C_source_phi_linkage_constructed",
        "C_source_phi_zero_derived",
        "phi_source_theorem_linkage_obligation_discharged",
        "A_source_route_imported",
        "A_sector_route_imported",
        "psi_A_sourced_Maxwell_imported",
        "psi_A_sourced_route_imported",
        "QFT_GR_source_route_imported",
        "J_current_imported",
        "gap_1_through_gap_8_discharged",
        "general_C_k_closure",
        "C_k_rule_promoted",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "action_embedding_claimed",
        "action_variation_executed",
        "phi_sector_closure_claimed",
        "full_scalar_qft_closure_claimed",
        "full_scalar_QFT_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[flag] is False, flag

    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert review["scoped_lean_targets_status_for_review"] == "PASSED_SERIAL_RERUN"
    assert review["full_toeformal_aggregate_passed"] is False


def test_phi_source_standalone_attempt_result_review_rotates_to_execution() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    report = _rel(DEFAULT_OUT)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=consumed_target(),
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert is_current is True

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    attempt = _workstream(registry, attempt_target())
    assert attempt["status"] == "paused"
    assert attempt["authorization_evidence"] == _rel(ATTEMPT_LEAN_PACKET_PATH)
    assert attempt["report"] == _rel(ATTEMPT_OUT)
    assert attempt["attempt_preparation_result"] == ATTEMPT_OUTCOME
    assert attempt["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert attempt["selected_next_target"] == consumed_target()

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["attempt_preparation_result"] == ATTEMPT_OUTCOME
    assert consumed["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["C_source_phi_residual_definition"] == (
        C_SOURCE_PHI_RESIDUAL_DEFINITION
    )
    assert consumed["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert consumed["on_shell_condition"] == ON_SHELL_CONDITION
    assert consumed["theorem_discharged"] == "no"
    assert consumed["C_source_phi_discharged"] == "no"
    assert consumed["A_source_route_imported"] == "no"
    assert consumed["psi_A_sourced_Maxwell_imported"] == "no"
    assert consumed["QFT_GR_source_route_imported"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["authorized_next_strict_target"] == NEXT_TARGET
    assert active["report"] == report
    assert active["consumed_target"] == consumed_target()
    assert active["review_result"] == OUTCOME_ID
    assert active["strict_review_result"] == STRICT_REVIEW_RESULT
    assert active["execution_result"] == "PENDING"
    assert active["selected_next_target"] == "PENDING"
    assert active["C_source_phi_residual_definition"] == C_SOURCE_PHI_RESIDUAL_DEFINITION
    assert active["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert active["on_shell_condition"] == ON_SHELL_CONDITION
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["C_source_phi_discharged"] == "no"
    assert active["phi_sector_closure_claimed"] == "no"
    assert active["full_scalar_qft_closure_claimed"] == "no"
    assert active["qft_gr_closure_claimed"] == "no"
    assert active["old_omnibus_tests_not_active_acceptance_authority"] == "yes"
    assert active["master_action_promoted"] == "no"


def test_phi_source_standalone_attempt_result_review_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_PATH,
            CURRENT_TARGET_PATH,
            CURRENT_AUTHORITY_PATH,
            TOE_FORMAL_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            ROADMAP_PATH,
            STRICT_MAP_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        STRICT_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "PhiSourceTheoremLinkageAttemptFromStandalonePhiRouteResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_EXECUTION_OUTCOME,
        STRICT_SUGGESTED_EXECUTION_OUTCOME,
        C_SOURCE_PHI_RESIDUAL_DEFINITION,
        RESIDUAL_IDENTITY_FORM,
        ON_SHELL_RESIDUAL_FORM,
        ON_SHELL_CONDITION,
        TARGET_CONCLUSION,
        "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_REVIEW_OUTCOME_v0",
        "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "no theorem execution during review",
        "no theorem discharge during review",
        "no phi-sector closure",
        "no full scalar/QFT closure",
        "no QFT-GR closure",
        "no EM-QFT closure",
        "no general C_k closure",
        "no action embedding",
        "no variation",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_phi_source_standalone_attempt_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review_gate.py"
    )
