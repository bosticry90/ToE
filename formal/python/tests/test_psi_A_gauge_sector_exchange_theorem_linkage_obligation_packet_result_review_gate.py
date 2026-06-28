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
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_report import (
    DEFAULT_OUT as PACKET_OUT,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    STRICT_PACKET_RESULT as PACKET_STRICT_OUTCOME,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review_report import (
    ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    ACCEPTED_REVIEW_FINDINGS,
    ACCEPTED_SOURCED_MAXWELL_ROUTE,
    ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
    ATTEMPT_PROOF_SKETCH,
    BASIS,
    BLOCKED_CLAIMS,
    CURRENT_DEFINITION,
    DEFAULT_OUT,
    DOMAIN_BOUNDARY_ASSUMPTIONS,
    FIELD_STRENGTH_OBJECT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_POST_ATTEMPT_REVIEW_KIND,
    LIKELY_POST_ATTEMPT_REVIEW_TARGET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATION,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_REVIEW_RESULT,
    TARGET,
    THEOREM_SHAPE_GIVEN,
    THEOREM_SHAPE_THEN,
    THEOREM_TARGET_STATEMENT,
    WATCH_ITEMS,
    build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_report import (
    DEFAULT_OUT as ATTEMPT_OUT,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    STRICT_ATTEMPT_PREPARATION_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review_report.py"
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
    return "review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result"


def packet_target() -> str:
    return "prepare_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet"


def test_psi_A_gauge_sector_exchange_packet_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_gauge_sector_exchange_packet_result_review_accepts_scope() -> None:
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
    assert review["likely_post_attempt_review_target"] == (
        LIKELY_POST_ATTEMPT_REVIEW_TARGET
    )
    assert review["likely_post_attempt_review_kind"] == LIKELY_POST_ATTEMPT_REVIEW_KIND
    assert review["attempt_preparation_recommended_outcome"] == (
        ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
    )
    assert review["attempt_proof_sketch"] == ATTEMPT_PROOF_SKETCH
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert (
        build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review()
        == review
    )


def test_psi_A_gauge_sector_exchange_packet_result_review_preserves_target_and_watch_items() -> None:
    review = _json(DEFAULT_OUT)

    assert review["theorem_shape"] == {
        "given": THEOREM_SHAPE_GIVEN,
        "then": THEOREM_SHAPE_THEN,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
    }
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["T_A_policy"] == "T_A^{mu nu} policy"
    assert review["field_strength_object"] == FIELD_STRENGTH_OBJECT
    assert review["current_object"] == "J object"
    assert review["current_definition"] == CURRENT_DEFINITION
    assert review["domain_boundary_assumptions"] == DOMAIN_BOUNDARY_ASSUMPTIONS
    assert (
        review["accepted_gauge_stress_energy_divergence_identity"]
        == ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
    )
    assert review["accepted_sourced_maxwell_route"] == ACCEPTED_SOURCED_MAXWELL_ROUTE
    assert review["watch_items"] == WATCH_ITEMS
    assert review["watch_item_count"] == 9
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


def test_psi_A_gauge_sector_exchange_packet_result_review_records_lean_status() -> None:
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


def test_psi_A_gauge_sector_exchange_packet_result_review_rotates_to_attempt_preparation() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    assert (
        assert_historical_target_recorded(
            payload=registry,
            previous_target=consumed_target(),
            live_target=NEXT_TARGET,
            evidence=evidence,
            lane=NEXT_TARGET,
        )
        is False
    )

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert LIKELY_POST_ATTEMPT_REVIEW_TARGET in registry["next_strict_target_coverage"]

    packet = workstream(packet_target(), registry)
    assert packet["status"] == "paused"
    assert packet["authorization_evidence"] == _rel(PACKET_LEAN_PACKET_PATH)
    assert packet["report"] == _rel(PACKET_OUT)
    assert packet["packet_result"] == PACKET_OUTCOME

    review_row = workstream(consumed_target(), registry)
    assert review_row["status"] == "paused"
    assert review_row["authorization_evidence"] == evidence
    assert review_row["report"] == _rel(DEFAULT_OUT)
    assert review_row["packet_result"] == PACKET_OUTCOME
    assert review_row["strict_packet_result"] == PACKET_STRICT_OUTCOME
    assert review_row["review_result"] == OUTCOME_ID
    assert review_row["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review_row["selected_next_target"] == NEXT_TARGET
    assert review_row["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review_row["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review_row["watch_items"] == "; ".join(WATCH_ITEMS)
    assert review_row["proof_attempt_executed"] == "no"
    assert review_row["theorem_discharged"] == "no"
    assert review_row["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == LIKELY_POST_ATTEMPT_REVIEW_TARGET
    assert active["active_lane"] == LIKELY_POST_ATTEMPT_REVIEW_TARGET
    assert active["authorization_evidence"] == _rel(ATTEMPT_LEAN_PACKET_PATH)
    assert active["report"] == _rel(ATTEMPT_OUT)
    assert active["consumed_target"] == NEXT_TARGET
    assert active["packet_result"] == ATTEMPT_OUTCOME
    assert active["attempt_preparation_result"] == ATTEMPT_OUTCOME
    assert (
        active["strict_attempt_preparation_result"]
        == STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert active["review_result"] == "PENDING"
    assert active["selected_next_target"] == (
        "execute_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
    )
    assert active["selected_next_target_kind"] == (
        "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_execution"
    )
    assert active["selected_obligation"] == OBLIGATION
    assert active["basis"] == BASIS
    assert active["proof_style"] == PROOF_STYLE
    assert active["target"] == TARGET
    assert active["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert active["watch_items"] == "; ".join(WATCH_ITEMS)
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_gauge_sector_exchange_packet_result_review_mirrors() -> None:
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
        "PsiAGaugeSectorExchangeTheoremLinkageObligationPacketResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_POST_ATTEMPT_REVIEW_TARGET,
        ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
        OBLIGATION,
        BASIS,
        PROOF_STYLE,
        THEOREM_TARGET_STATEMENT,
        WATCH_ITEMS[0],
        WATCH_ITEMS[-1],
        LEAN_STATUS_WORDING_FOR_PACKET,
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "gauge stress-energy divergence identity",
        "sourced Maxwell route",
        "same F and J objects",
        "sign and index conventions",
        "no proof execution during review",
        "no theorem discharge during review",
        "no C_k rule promotion",
        "no C_k action embedding",
        "no C_k variation",
        "no full Maxwell closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_gauge_sector_exchange_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review_gate.py"
    )
