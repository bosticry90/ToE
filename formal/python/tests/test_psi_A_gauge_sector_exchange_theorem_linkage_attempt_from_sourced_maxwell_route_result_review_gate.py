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
    skip_if_not_current_target,
    workstream,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_report import (
    ATTEMPT_PREPARATION_RESULT,
    DEFAULT_OUT as ATTEMPT_PACKET_PATH,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    OUTCOME_ID as ATTEMPT_PACKET_OUTCOME,
    STRICT_ATTEMPT_PREPARATION_RESULT,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review_report import (
    ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    ACCEPTED_REVIEW_FINDINGS,
    ACCEPTED_SOURCED_MAXWELL_ROUTE,
    CONSUMED_TARGET,
    CONSUMED_TARGET_KIND,
    DEFAULT_OUT,
    EXCHANGE_DEPENDENCY_CHAIN,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PLANNED_PROOF_STEPS,
    REVIEW_BLOCKED_CLAIMS,
    REVIEW_RESULT,
    ROUTE_GIVEN,
    ROUTE_THEN,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    WATCH_ITEMS,
    build_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review_report.py"
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


def test_psi_A_gauge_sector_exchange_attempt_result_review_files_exist() -> None:
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


def test_psi_A_gauge_sector_exchange_attempt_result_review_accepts_preparation() -> None:
    review = _json(DEFAULT_OUT)

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["reviewed"] is True
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
    assert review["attempt_packet_outcome"] == ATTEMPT_PACKET_OUTCOME
    assert review["attempt_preparation_result"] == ATTEMPT_PREPARATION_RESULT
    assert (
        review["attempt_packet_strict_outcome"]
        == STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert review["gauge_sector_exchange_attempt_prepared"] is True
    assert review["sourced_maxwell_input_preserved"] is True
    assert review["gauge_stress_energy_divergence_identity_preserved"] is True
    assert review["same_F_and_J_objects_preserved"] is True
    assert review["sign_and_index_conventions_preserved"] is True
    assert review["accepted_sourced_maxwell_route"] == ACCEPTED_SOURCED_MAXWELL_ROUTE
    assert (
        review["accepted_gauge_stress_energy_divergence_identity"]
        == ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
    )
    assert review["route_given"] == ROUTE_GIVEN
    assert review["route_then"] == ROUTE_THEN
    assert review["target_rule"] == TARGET
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["planned_proof_steps"] == PLANNED_PROOF_STEPS
    assert review["plain_meaning"] == PLAIN_MEANING
    assert review["watch_items"] == WATCH_ITEMS
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["exchange_dependency_chain"] == EXCHANGE_DEPENDENCY_CHAIN
    assert (
        build_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review()
        == review
    )


def test_psi_A_gauge_sector_exchange_attempt_result_review_preserves_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["review_blocked_claims"] == REVIEW_BLOCKED_CLAIMS
    assert review["review_executes_attempt"] is False
    assert review["proof_execution_authorized"] is False
    assert review["proof_execution_authorized_by_review_for_next_target"] is True
    assert review["proof_attempt_executed"] is False
    assert review["theorem_discharged"] is False
    assert review["theorem_linkage_obligation_discharged"] is False
    assert review["gap_1_through_gap_8_discharged"] is False
    assert review["rule_promoted"] is False
    assert review["C_k_action_embedding_claimed"] is False
    assert review["C_k_action_variation_executed"] is False
    assert review["full_maxwell_closure_claimed"] is False
    assert review["em_qft_closure_claimed"] is False
    assert review["qft_gr_closure_claimed"] is False
    assert review["gr_qm_closure_claimed"] is False
    assert review["seam_closure_claim"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False


def test_psi_A_gauge_sector_exchange_attempt_result_review_records_lean_status() -> None:
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


def test_psi_A_gauge_sector_exchange_attempt_result_review_rotates_to_execution() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    skip_if_not_current_target(registry, NEXT_TARGET)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    assert (
        assert_historical_target_recorded(
            payload=registry,
            previous_target=CONSUMED_TARGET,
            live_target=NEXT_TARGET,
            evidence=evidence,
            lane=NEXT_TARGET,
        )
        is True
    )

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    attempt = workstream(
        "prepare_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route",
        registry,
    )
    assert attempt["status"] == "paused"
    assert attempt["authorization_evidence"] == _rel(ATTEMPT_LEAN_PACKET_PATH)
    assert attempt["report"] == _rel(ATTEMPT_PACKET_PATH)
    assert attempt["attempt_preparation_result"] == ATTEMPT_PREPARATION_RESULT
    assert attempt["selected_next_target"] == CONSUMED_TARGET
    assert attempt["proof_attempt_executed"] == "no"
    assert attempt["theorem_discharged"] == "no"

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
        active["strict_suggested_execution_outcome"]
        == STRICT_SUGGESTED_EXECUTION_OUTCOME
    )
    assert active["selected_next_target"] == CONSUMED_TARGET
    assert active["selected_next_target_kind"] == CONSUMED_TARGET_KIND
    assert active["proof_execution_authorized"] == "yes"
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_gauge_sector_exchange_attempt_result_review_mirrors() -> None:
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
        "PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_EXECUTION_OUTCOME,
        STRICT_SUGGESTED_EXECUTION_OUTCOME,
        THEOREM_TARGET_STATEMENT,
        PLANNED_PROOF_STEPS[0],
        PLANNED_PROOF_STEPS[-1],
        WATCH_ITEMS[0],
        WATCH_ITEMS[-1],
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_RESULT_REVIEW_OUTCOME_v0",
        "no theorem execution during review",
        "no theorem discharge during review",
        "no C_k rule promotion",
        "no full Maxwell closure",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_gauge_sector_exchange_attempt_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review_gate.py"
    )
