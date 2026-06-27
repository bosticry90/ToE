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
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_packet_report import (
    BASIS,
    DEFAULT_OUT,
    EXPANDED_CANCELLATION_CHAIN,
    EXPANDED_CANCELLATION_CHAIN_STATEMENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GAUGE_EXCHANGE_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATION,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_RESULT,
    PLAIN_MEANING,
    PROOF_STYLE,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_PACKET_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_psi_A_total_conservation_theorem_linkage_obligation_packet,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_packet_result_review_report import (
    DEFAULT_OUT as REVIEW_OUT,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as ATTEMPT_PREPARATION_TARGET,
    NEXT_TARGET_KIND as ATTEMPT_PREPARATION_TARGET_KIND,
    OUTCOME_ID as REVIEW_OUTCOME,
    PROOF_ATTEMPT_WATCH_ITEMS,
    STRICT_REVIEW_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_total_conservation_theorem_linkage_obligation_packet_report.py"
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
    return "prepare_psi_A_total_conservation_theorem_linkage_obligation_packet"


def test_psi_A_total_conservation_packet_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_total_conservation_packet_scopes_exchange_cancellation_target() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == PACKET_RESULT
    assert packet["strict_packet_result"] == STRICT_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == consumed_target()
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["likely_follow_on_target_after_review"] == (
        LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW
    )
    assert packet["obligation"] == OBLIGATION
    assert packet["basis"] == BASIS
    assert packet["proof_style"] == PROOF_STYLE
    assert packet["target"] == TOTAL_CONSERVATION_CONCLUSION
    assert packet["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert packet["expanded_cancellation_chain"] == EXPANDED_CANCELLATION_CHAIN
    assert (
        packet["expanded_cancellation_chain_statement"]
        == EXPANDED_CANCELLATION_CHAIN_STATEMENT
    )
    assert build_psi_A_total_conservation_theorem_linkage_obligation_packet() == packet


def test_psi_A_total_conservation_packet_preserves_boundary() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["theorem_shape"] == {
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
    assert packet["proof_execution_authorized"] is False
    assert packet["proof_attempt_executed"] is False
    assert packet["theorem_discharged"] is False
    assert packet["theorem_linkage_obligation_discharged"] is False
    assert packet["proof_debt_discharged"] is False
    assert packet["gap_1_through_gap_8_discharged"] is False
    assert packet["rule_promoted"] is False
    assert packet["C_k_action_embedding_claimed"] is False
    assert packet["C_k_action_variation_executed"] is False
    assert packet["full_maxwell_closure_claimed"] is False
    assert packet["em_qft_closure_claimed"] is False
    assert packet["qft_gr_closure_claimed"] is False
    assert packet["gr_qm_closure_claimed"] is False
    assert packet["seam_closure_claim"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["master_action_promoted"] is False


def test_psi_A_total_conservation_packet_records_lean_status() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_PACKET
    assert (
        packet["full_toeformal_aggregate_status_for_packet"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
    )
    assert (
        packet["scoped_lean_targets_status_for_packet"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
    )
    assert packet["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(packet)


def test_psi_A_total_conservation_packet_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    review_evidence = _rel(REVIEW_LEAN_PACKET_PATH)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    assert_historical_target_recorded(
        payload=registry,
        previous_target=consumed_target(),
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    packet_row = workstream(consumed_target(), registry)
    assert packet_row["status"] == "paused"
    assert packet_row["authorization_evidence"] == evidence
    assert packet_row["report"] == _rel(DEFAULT_OUT)
    assert packet_row["packet_result"] == OUTCOME_ID
    assert packet_row["strict_packet_result"] == STRICT_PACKET_RESULT
    assert packet_row["selected_next_target"] == NEXT_TARGET
    assert packet_row["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet_row["obligation"] == OBLIGATION
    assert packet_row["basis"] == BASIS
    assert packet_row["proof_style"] == PROOF_STYLE
    assert packet_row["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert packet_row["expanded_cancellation_chain"] == EXPANDED_CANCELLATION_CHAIN_STATEMENT
    assert packet_row["proof_attempt_executed"] == "no"
    assert packet_row["theorem_discharged"] == "no"
    assert packet_row["rule_promoted"] == "no"

    review_row = workstream(NEXT_TARGET, registry)
    assert review_row["status"] == "paused"
    assert review_row["authorization_evidence"] == review_evidence
    assert review_row["report"] == _rel(REVIEW_OUT)
    assert review_row["review_result"] == REVIEW_OUTCOME
    assert review_row["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review_row["selected_next_target"] == ATTEMPT_PREPARATION_TARGET
    assert review_row["selected_next_target_kind"] == ATTEMPT_PREPARATION_TARGET_KIND
    assert review_row["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review_row["proof_attempt_watch_items"] == PROOF_ATTEMPT_WATCH_ITEMS
    assert review_row["proof_attempt_executed"] == "no"
    assert review_row["theorem_discharged"] == "no"
    assert review_row["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == ATTEMPT_PREPARATION_TARGET
    assert active["active_lane"] == ATTEMPT_PREPARATION_TARGET
    assert active["authorization_evidence"] == review_evidence
    assert active["authorized_next_strict_target"] == ATTEMPT_PREPARATION_TARGET
    assert active["consumed_target"] == NEXT_TARGET
    assert active["packet_result"] == "PENDING"
    assert active["review_result"] == REVIEW_OUTCOME
    assert active["selected_next_target_kind"] == ATTEMPT_PREPARATION_TARGET_KIND
    assert active["proof_attempt_watch_items"] == PROOF_ATTEMPT_WATCH_ITEMS
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_total_conservation_packet_mirrors() -> None:
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
        STRICT_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "PsiATotalConservationTheoremLinkageObligationPacket",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW,
        OBLIGATION,
        BASIS,
        PROOF_STYLE,
        THEOREM_TARGET_STATEMENT,
        EXPANDED_CANCELLATION_CHAIN_STATEMENT,
        LEAN_STATUS_WORDING_FOR_PACKET,
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_OUTCOME_v0",
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_PACKET_NONCLAIM_BOUNDARY_v0",
        "no proof execution",
        "no theorem discharge",
        "no GAP-1 through GAP-8 discharge",
        "no C_k rule promotion",
        "no C_k action embedding",
        "no C_k variation",
        "no full Maxwell closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_total_conservation_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_total_conservation_theorem_linkage_obligation_packet_gate.py"
    )
