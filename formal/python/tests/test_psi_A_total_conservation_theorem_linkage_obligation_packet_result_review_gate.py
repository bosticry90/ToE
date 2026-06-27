from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    workstream,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_packet_report import (
    DEFAULT_OUT as PACKET_OUT,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_packet_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
    BLOCKED_CLAIMS,
    DEFAULT_OUT,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GAUGE_EXCHANGE_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PROOF_ATTEMPT_WATCH_ITEMS,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_REVIEW_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_psi_A_total_conservation_theorem_linkage_obligation_packet_result_review,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_report import (
    DEFAULT_OUT as ATTEMPT_OUT,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    NEXT_TARGET as ATTEMPT_REVIEW_TARGET,
    NEXT_TARGET_KIND as ATTEMPT_REVIEW_TARGET_KIND,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    ATTEMPT_WATCH_ITEMS,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_result_review_report import (
    DEFAULT_OUT as ATTEMPT_RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as ATTEMPT_RESULT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as ATTEMPT_EXECUTION_TARGET,
    NEXT_TARGET_KIND as ATTEMPT_EXECUTION_TARGET_KIND,
    OUTCOME_ID as ATTEMPT_RESULT_REVIEW_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME as ATTEMPT_SUGGESTED_EXECUTION_OUTCOME,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_result_review_report import (
    CLOSEOUT_OUTCOME,
    CLOSEOUT_STATEMENT,
    DEFAULT_OUT as EXECUTION_RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as CLOSEOUT_TARGET,
    NEXT_TARGET_KIND as CLOSEOUT_TARGET_KIND,
    OUTCOME_ID as EXECUTION_RESULT_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as EXECUTION_RESULT_REVIEW_STRICT_OUTCOME,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_closeout_report import (
    DEFAULT_OUT as CLOSEOUT_OUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    NEXT_TARGET as CLOSEOUT_REVIEW_TARGET,
    NEXT_TARGET_KIND as CLOSEOUT_REVIEW_TARGET_KIND,
    OUTCOME_ID as CLOSEOUT_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_total_conservation_theorem_linkage_obligation_packet_result_review_report.py"
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


def consumed_target() -> str:
    return "review_psi_A_total_conservation_theorem_linkage_obligation_packet_result"


def packet_target() -> str:
    return "prepare_psi_A_total_conservation_theorem_linkage_obligation_packet"


def test_psi_A_total_conservation_packet_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_total_conservation_packet_result_review_accepts_scope() -> None:
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
    assert review["attempt_preparation_recommended_outcome"] == (
        ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
    )
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert (
        build_psi_A_total_conservation_theorem_linkage_obligation_packet_result_review()
        == review
    )


def test_psi_A_total_conservation_packet_result_review_preserves_target_and_watch_items() -> None:
    review = _json(DEFAULT_OUT)

    assert review["theorem_shape"] == {
        "given": [
            GAUGE_EXCHANGE_ROUTE,
            MATTER_EXCHANGE_ROUTE,
            TOTAL_STRESS_ENERGY_DEFINITION,
        ],
        "then": TOTAL_CONSERVATION_CONCLUSION,
        "expanded": EXPANDED_CANCELLATION_CHAIN,
        "expanded_statement": EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        "plain_meaning": PLAIN_MEANING,
    }
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["proof_attempt_watch_items"] == PROOF_ATTEMPT_WATCH_ITEMS
    assert review["proof_attempt_watch_item_count"] == 8
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["review_executes_proof"] is False
    assert review["proof_execution_authorized"] is False
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


def test_psi_A_total_conservation_packet_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_PACKET
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
    )
    assert (
        review["scoped_lean_targets_status_for_review"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
    )
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_psi_A_total_conservation_packet_result_review_rotates_to_attempt_preparation() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    attempt_evidence = _rel(ATTEMPT_LEAN_PACKET_PATH)
    execution_evidence = (
        "formal/toe_formal/ToeFormal/Derivation/"
        "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesExecution.lean"
    )
    execution_report = (
        "formal/docs/release/"
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_"
        "EXECUTION_20260627_v0.json"
    )
    execution_outcome = ATTEMPT_SUGGESTED_EXECUTION_OUTCOME
    execution_result_review_evidence = _rel(EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH)
    execution_result_review_report = _rel(EXECUTION_RESULT_REVIEW_OUT)
    closeout_evidence = _rel(CLOSEOUT_LEAN_PACKET_PATH)
    closeout_report = _rel(CLOSEOUT_OUT)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    packet = workstream(packet_target(), registry)
    assert packet["status"] == "paused"
    assert packet["authorization_evidence"] == _rel(PACKET_LEAN_PACKET_PATH)
    assert packet["report"] == _rel(PACKET_OUT)
    assert packet["packet_result"] == PACKET_OUTCOME

    review_row = workstream(consumed_target(), registry)
    assert review_row["status"] == "paused"
    assert review_row["authorization_evidence"] == evidence
    assert review_row["report"] == _rel(DEFAULT_OUT)
    assert review_row["review_result"] == OUTCOME_ID
    assert review_row["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review_row["selected_next_target"] == NEXT_TARGET
    assert review_row["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review_row["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review_row["proof_attempt_watch_items"] == PROOF_ATTEMPT_WATCH_ITEMS
    assert review_row["proof_attempt_executed"] == "no"
    assert review_row["theorem_discharged"] == "no"
    assert review_row["rule_promoted"] == "no"

    attempt = workstream(NEXT_TARGET, registry)
    assert attempt["status"] == "paused"
    assert attempt["authorization_evidence"] == attempt_evidence
    assert attempt["report"] == _rel(ATTEMPT_OUT)
    assert attempt["packet_result"] == ATTEMPT_OUTCOME
    assert attempt["attempt_preparation_result"] == ATTEMPT_OUTCOME
    assert attempt["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert attempt["selected_next_target"] == ATTEMPT_REVIEW_TARGET
    assert attempt["selected_next_target_kind"] == ATTEMPT_REVIEW_TARGET_KIND
    assert attempt["watch_items"] == ATTEMPT_WATCH_ITEMS
    assert attempt["proof_attempt_executed"] == "no"
    assert attempt["theorem_discharged"] == "no"
    assert attempt["rule_promoted"] == "no"

    attempt_review = workstream(ATTEMPT_REVIEW_TARGET, registry)
    assert attempt_review["status"] == "paused"
    assert attempt_review["authorization_evidence"] == execution_result_review_evidence
    assert attempt_review["report"] == execution_result_review_report
    assert attempt_review["execution_result"] == execution_outcome
    assert attempt_review["review_result"] == EXECUTION_RESULT_REVIEW_OUTCOME
    assert attempt_review["strict_review_result"] == (
        EXECUTION_RESULT_REVIEW_STRICT_OUTCOME
    )
    assert attempt_review["selected_next_target"] == CLOSEOUT_TARGET
    assert attempt_review["selected_next_target_kind"] == CLOSEOUT_TARGET_KIND
    assert attempt_review["review_executes_attempt"] == "no"
    assert attempt_review["proof_execution_authorized"] == "no"
    assert attempt_review["proof_attempt_executed"] == "yes"
    assert attempt_review["theorem_discharged"] == "yes"
    assert attempt_review["rule_promoted"] == "no"

    executed = workstream(ATTEMPT_EXECUTION_TARGET, registry)
    assert executed["status"] == "paused"
    assert executed["authorization_evidence"] == execution_evidence
    assert executed["report"] == execution_report
    assert executed["execution_result"] == execution_outcome
    assert executed["selected_next_target"] == ATTEMPT_REVIEW_TARGET
    assert executed["proof_attempt_executed"] == "yes"
    assert executed["theorem_discharged"] == "yes"
    assert executed["rule_promoted"] == "no"

    closeout = workstream(CLOSEOUT_TARGET, registry)
    assert closeout["status"] == "paused"
    assert closeout["authorization_evidence"] == closeout_evidence
    assert closeout["report"] == closeout_report
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
    assert closeout["selected_next_target_kind"] == CLOSEOUT_REVIEW_TARGET_KIND
    assert closeout["local_psi_A_total_conservation_obligation_closed"] == "yes"
    assert closeout["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == CLOSEOUT_REVIEW_TARGET
    assert active["active_lane"] == CLOSEOUT_REVIEW_TARGET
    assert active["authorization_evidence"] == closeout_evidence
    assert active["authorized_next_strict_target"] == CLOSEOUT_REVIEW_TARGET
    assert active["consumed_target"] == CLOSEOUT_TARGET
    assert active["packet_result"] == CLOSEOUT_RESULT
    assert active["closeout_result"] == CLOSEOUT_RESULT
    assert active["review_result"] == "PENDING"
    assert active["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
    assert active["selected_next_target_kind"] == CLOSEOUT_REVIEW_TARGET_KIND
    assert active["watch_items"] == ATTEMPT_WATCH_ITEMS
    assert active["closeout_statement"] == CLOSEOUT_STATEMENT
    assert active["proof_execution_authorized"] == "no"
    assert active["proof_attempt_executed"] == "yes"
    assert active["theorem_discharged"] == "yes"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_total_conservation_packet_result_review_mirrors() -> None:
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
        "PsiATotalConservationTheoremLinkageObligationPacketResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
        THEOREM_TARGET_STATEMENT,
        EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        LEAN_STATUS_WORDING_FOR_PACKET,
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "same F object",
        "same J object",
        "same index placement",
        "same sign convention",
        "same connection/covariant derivative",
        "linearity of nabla over addition",
        "valid T_total definition",
        "shared domain and boundary assumptions",
        "no proof execution during review",
        "no theorem discharge during review",
        "no GAP-1 through GAP-8 discharge",
        "no C_k rule promotion",
        "no C_k action embedding",
        "no C_k variation",
        "no full Maxwell closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_total_conservation_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_total_conservation_theorem_linkage_obligation_packet_result_review_gate.py"
    )
