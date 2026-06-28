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
    ACCEPTED_PACKET_FINDINGS,
    ATTEMPT_PREPARATION_RESULT,
    BLOCKED_CLAIMS,
    DEFAULT_OUT,
    DIRAC_EQUATION_SHAPE,
    ADJOINT_DIRAC_EQUATION_SHAPE,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_POST_REVIEW_TARGET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PLANNED_PROOF_STEPS,
    ROUTE_GIVEN,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    WATCH_ITEMS,
    build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair,
)
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result_review_report import (
    DEFAULT_OUT as REVIEW_OUT,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_report.py"
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
    return "prepare_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair"


def review_target() -> str:
    return "review_psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result"


def test_psi_A_matter_sector_exchange_attempt_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_matter_sector_exchange_attempt_indexes_dirac_pair_route() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == ATTEMPT_PREPARATION_RESULT
    assert packet["attempt_preparation_result"] == ATTEMPT_PREPARATION_RESULT
    assert (
        packet["strict_attempt_preparation_result"]
        == STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == consumed_target()
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["likely_post_review_target"] == LIKELY_POST_REVIEW_TARGET
    assert packet["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert packet["dirac_equation_shape"] == DIRAC_EQUATION_SHAPE
    assert packet["adjoint_dirac_equation_shape"] == ADJOINT_DIRAC_EQUATION_SHAPE
    assert packet["planned_proof_steps"] == PLANNED_PROOF_STEPS
    assert packet["watch_items"] == WATCH_ITEMS
    assert packet["accepted_packet_findings"] == ACCEPTED_PACKET_FINDINGS
    assert (
        build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair()
        == packet
    )


def test_psi_A_matter_sector_exchange_attempt_preserves_route_and_boundary() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["theorem_shape"] == {
        "given": ROUTE_GIVEN,
        "then": TARGET,
        "planned_proof_steps": PLANNED_PROOF_STEPS,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
    }
    assert packet["blocked_claims"] == BLOCKED_CLAIMS
    assert packet["preparation_executes_proof"] is False
    assert packet["proof_execution_authorized"] is False
    assert packet["proof_attempt_executed"] is False
    assert packet["theorem_discharged"] is False
    assert packet["theorem_linkage_obligation_discharged"] is False
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


def test_psi_A_matter_sector_exchange_attempt_records_lean_status() -> None:
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


def test_psi_A_matter_sector_exchange_attempt_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=consumed_target(),
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    if is_current:
        assert NEXT_TARGET not in registry["paused_lanes"]
    else:
        assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    prior_review = workstream(review_target(), registry)
    assert prior_review["status"] == "paused"
    assert prior_review["authorization_evidence"] == _rel(REVIEW_LEAN_PACKET_PATH)
    assert prior_review["report"] == _rel(REVIEW_OUT)
    assert prior_review["review_result"] == REVIEW_OUTCOME
    assert prior_review["strict_review_result"] == STRICT_REVIEW_RESULT

    attempt = workstream(consumed_target(), registry)
    assert attempt["status"] == "paused"
    assert attempt["authorization_evidence"] == evidence
    assert attempt["report"] == _rel(DEFAULT_OUT)
    assert attempt["packet_result"] == OUTCOME_ID
    assert attempt["attempt_preparation_result"] == OUTCOME_ID
    assert attempt["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert attempt["planned_proof_steps"] == PLANNED_PROOF_STEPS
    assert attempt["watch_items"] == "; ".join(WATCH_ITEMS)
    assert attempt["proof_attempt_executed"] == "no"
    assert attempt["theorem_discharged"] == "no"
    assert attempt["rule_promoted"] == "no"

    result_review = workstream(NEXT_TARGET, registry)
    active = active_workstream(registry)
    if active["workstream_id"] == NEXT_TARGET:
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        reviewed = active
        review_target_is_current = True
    else:
        assert result_review["status"] == "paused"
        reviewed = result_review
        review_target_is_current = False
    assert reviewed["attempt_preparation_result"] == OUTCOME_ID
    assert reviewed["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    if review_target_is_current:
        assert reviewed["consumed_target"] == consumed_target()
        assert reviewed["authorization_evidence"] == evidence
        assert reviewed["report"] == _rel(DEFAULT_OUT)
        assert reviewed["packet_result"] == OUTCOME_ID
        assert reviewed["review_result"] == "PENDING"
    else:
        assert reviewed["consumed_target"] == NEXT_TARGET
        assert reviewed["authorization_evidence"] != evidence
        assert reviewed["report"] != _rel(DEFAULT_OUT)
        assert reviewed["packet_result"] != OUTCOME_ID
        assert reviewed["review_result"] != "PENDING"
    assert reviewed["selected_next_target"] == LIKELY_POST_REVIEW_TARGET
    assert reviewed["selected_next_target_kind"] == (
        "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution"
    )
    assert reviewed["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert reviewed["planned_proof_steps"] == PLANNED_PROOF_STEPS
    assert reviewed["watch_items"] == "; ".join(WATCH_ITEMS)
    assert reviewed["proof_attempt_executed"] == "no"
    assert reviewed["theorem_discharged"] == "no"
    assert reviewed["rule_promoted"] == "no"
    assert reviewed["master_action_promoted"] == "no"


def test_psi_A_matter_sector_exchange_attempt_mirrors() -> None:
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
        STRICT_ATTEMPT_PREPARATION_RESULT,
        PACKET_CLASSIFICATION,
        "PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPair",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_POST_REVIEW_TARGET,
        THEOREM_TARGET_STATEMENT,
        PLANNED_PROOF_STEPS[0],
        PLANNED_PROOF_STEPS[-1],
        WATCH_ITEMS[0],
        WATCH_ITEMS[-1],
        LEAN_STATUS_WORDING_FOR_PACKET,
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_OUTCOME_v0",
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_NONCLAIM_BOUNDARY_v0",
        "no theorem discharge during preparation",
        "no C_k rule promotion",
        "no C_k action embedding",
        "no C_k variation",
        "no multiplier route",
        "no penalty route",
        "no direct dynamical-law claim",
        "no full Maxwell closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_matter_sector_exchange_attempt_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_gate.py"
    )
