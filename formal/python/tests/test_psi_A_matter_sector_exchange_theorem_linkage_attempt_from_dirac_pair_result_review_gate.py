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
    workstream,
)
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_report import (
    ATTEMPT_PREPARATION_RESULT,
    DEFAULT_OUT as ATTEMPT_PACKET_PATH,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    PLANNED_PROOF_STEPS,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    WATCH_ITEMS,
)
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ADJOINT_DIRAC_EQUATION_SHAPE,
    CONSUMED_TARGET,
    CURRENT_DEFINITION,
    DEFAULT_OUT,
    DELICATE_WATCH_ITEMS,
    DIRAC_EQUATION_SHAPE,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REVIEW_BLOCKED_CLAIMS,
    REVIEW_RESULT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_BLOCKED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    T_PSI_POLICY,
    build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review_report.py"
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


def test_psi_A_matter_exchange_attempt_result_review_files_exist() -> None:
    for path in [
        ATTEMPT_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_matter_exchange_attempt_result_review_accepts_preparation() -> None:
    review = _json(DEFAULT_OUT)

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["suggested_execution_outcome"] == SUGGESTED_EXECUTION_OUTCOME
    assert (
        review["strict_suggested_execution_outcome"]
        == STRICT_SUGGESTED_EXECUTION_OUTCOME
    )
    assert (
        review["suggested_blocked_execution_outcome"]
        == SUGGESTED_BLOCKED_EXECUTION_OUTCOME
    )
    assert (
        build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review()
        == review
    )


def test_psi_A_matter_exchange_attempt_result_review_preserves_route() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["target_rule"] == TARGET
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["T_psi_policy"] == T_PSI_POLICY
    assert review["dirac_equation_shape"] == DIRAC_EQUATION_SHAPE
    assert review["adjoint_dirac_equation_shape"] == ADJOINT_DIRAC_EQUATION_SHAPE
    assert review["current_definition"] == CURRENT_DEFINITION
    assert review["planned_proof_steps"] == PLANNED_PROOF_STEPS
    assert review["watch_items"] == WATCH_ITEMS
    assert review["delicate_watch_items"] == DELICATE_WATCH_ITEMS
    assert "missing assumption" in review["delicate_route_caution"]
    assert review["matter_side_exchange_attempt_prepared"] is True
    assert review["target_equation_preserved"] is True
    assert review["dirac_equation_context_preserved"] is True
    assert review["adjoint_dirac_equation_context_preserved"] is True
    assert review["tpsi_policy_preserved"] is True
    assert review["current_definition_preserved"] is True
    assert review["watch_items_preserved"] is True


def test_psi_A_matter_exchange_attempt_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)

    assert review["blocked_claims"] == REVIEW_BLOCKED_CLAIMS
    assert review["gap_count"] == 8
    assert review["open_gap_count"] == 8
    assert review["closed_gap_count"] == 0
    assert review["proof_target_selected"] is True
    assert review["theorem_row_selected"] is True
    assert review["theorem_row_selected_for_execution"] is True
    assert review["proof_execution_authorized_by_review_for_next_target"] is True
    assert review["theorem_linkage_proof_attempt_authorized_for_next_target"] is True

    for key in [
        "proof_execution_authorized",
        "proof_target_execution_authorized",
        "proof_attempt_executed",
        "proof_debt_reduced",
        "proof_debt_discharged",
        "theorem_discharged",
        "theorem_linkage_completed",
        "theorem_linkage_obligation_discharged",
        "theorem_linkage_proof_attempt_authorized",
        "review_executes_attempt",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "direct_dynamical_law_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_psi_A_matter_exchange_attempt_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_REVIEW
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
    )
    assert (
        review["scoped_lean_targets_status_for_review"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
    )
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_psi_A_matter_exchange_attempt_result_review_rotates_to_execution() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    attempt = workstream("prepare_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair", registry)
    assert attempt["status"] == "paused"
    assert attempt["authorization_evidence"] == _rel(ATTEMPT_LEAN_PACKET_PATH)
    assert attempt["report"] == _rel(ATTEMPT_PACKET_PATH)
    assert attempt["attempt_preparation_result"] == ATTEMPT_PREPARATION_RESULT
    assert (
        attempt["strict_attempt_preparation_result"]
        == STRICT_ATTEMPT_PREPARATION_RESULT
    )

    reviewed = workstream(CONSUMED_TARGET, registry)
    assert reviewed["status"] == "paused"
    assert reviewed["authorization_evidence"] == evidence
    assert reviewed["report"] == _rel(DEFAULT_OUT)
    assert reviewed["review_result"] == OUTCOME_ID
    assert reviewed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert reviewed["selected_next_target"] == NEXT_TARGET
    assert reviewed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert reviewed["proof_attempt_executed"] == "no"
    assert reviewed["theorem_discharged"] == "no"
    assert reviewed["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == NEXT_TARGET
    assert active["active_lane"] == NEXT_TARGET
    assert active["authorization_evidence"] == evidence
    assert active["report"] == _rel(DEFAULT_OUT)
    assert active["consumed_target"] == CONSUMED_TARGET
    assert active["review_result"] == OUTCOME_ID
    assert active["strict_review_result"] == STRICT_REVIEW_RESULT
    assert active["execution_result"] == "PENDING"
    assert active["suggested_execution_outcome"] == SUGGESTED_EXECUTION_OUTCOME
    assert (
        active["suggested_blocked_execution_outcome"]
        == SUGGESTED_BLOCKED_EXECUTION_OUTCOME
    )
    assert active["selected_next_target"] == (
        "review_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result"
    )
    assert active["selected_next_target_kind"] == (
        "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review"
    )
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_matter_exchange_attempt_result_review_mirrors() -> None:
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
        "PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_EXECUTION_OUTCOME,
        STRICT_SUGGESTED_EXECUTION_OUTCOME,
        SUGGESTED_BLOCKED_EXECUTION_OUTCOME,
        TARGET,
        THEOREM_TARGET_STATEMENT,
        DIRAC_EQUATION_SHAPE,
        ADJOINT_DIRAC_EQUATION_SHAPE,
        CURRENT_DEFINITION,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "no theorem execution",
        "no theorem discharge",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_psi_A_matter_exchange_attempt_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review_gate.py"
    )
