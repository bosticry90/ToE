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
from formal.python.tools.A_source_theorem_linkage_obligation_packet_report import (
    DEFAULT_OUT as PACKET_OUT,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    STRICT_PACKET_RESULT as PACKET_STRICT_OUTCOME,
)
from formal.python.tools.A_source_theorem_linkage_obligation_packet_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
    BLOCKED_CLAIMS,
    C_SOURCE_A_SHORT_FORM,
    C_SOURCE_A_TARGET_STATEMENT,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_POST_ATTEMPT_REVIEW_TARGET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    STANDALONE_A_ROUTE,
    STANDALONE_A_ROUTE_ATTEMPT_SKETCH,
    STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
    STRICT_REVIEW_RESULT,
    build_A_source_theorem_linkage_obligation_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "A_source_theorem_linkage_obligation_packet_result_review_report.py"
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
    return "review_A_source_theorem_linkage_obligation_packet_result"


def packet_target() -> str:
    return "prepare_A_source_theorem_linkage_obligation_packet"


def test_A_source_packet_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_A_source_packet_result_review_accepts_standalone_scope() -> None:
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
    assert review["attempt_preparation_recommended_outcome"] == (
        ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
    )
    assert review["strict_attempt_preparation_recommended_outcome"] == (
        STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
    )
    assert review["standalone_A_route_attempt_sketch"] == STANDALONE_A_ROUTE_ATTEMPT_SKETCH
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert build_A_source_theorem_linkage_obligation_packet_result_review() == review


def test_A_source_packet_result_review_preserves_vacuum_route_and_blocks_psi_A_route() -> None:
    review = _json(DEFAULT_OUT)

    assert review["standalone_A_sector_route"] == STANDALONE_A_ROUTE
    assert review["standalone_A_sector_route_preserved"] is True
    assert review["C_source_A_short_form"] == C_SOURCE_A_SHORT_FORM
    assert review["C_source_A_target_statement"] == C_SOURCE_A_TARGET_STATEMENT
    assert review["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert review["accepted_A_sector_source_equation_to_freeze"] == (
        "nabla_mu T_A^{mu nu} = 0"
    )
    assert review["psi_A_sourced_maxwell_route"] == PSI_A_SOURCED_MAXWELL_ROUTE
    assert review["psi_A_sourced_route_substituted"] is False
    assert review["do_not_silently_substitute_psi_A_sourced_Maxwell_route"] is True
    assert review["route_contamination_guard"] == PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert "nabla_mu F^{mu alpha} = J^alpha" not in " ".join(
        review["standalone_A_route_attempt_sketch"]
    )


def test_A_source_packet_result_review_preserves_boundaries() -> None:
    review = _json(DEFAULT_OUT)

    for flag in [
        "review_executes_proof",
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_source_A_discharged",
        "A_source_theorem_linkage_obligation_discharged",
        "gap_1_through_gap_8_discharged",
        "general_C_k_closure",
        "C_k_dynamical_law_status",
        "C_k_rule_promoted",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "action_embedding_claimed",
        "action_variation_executed",
        "A_sector_closure_claimed",
        "sourced_maxwell_closure_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[flag] is False, flag

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_PACKET
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert review["scoped_lean_targets_status_for_review"] == "PASSED_SERIAL_RERUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_A_source_packet_result_review_rotates_to_standalone_attempt_preparation() -> None:
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

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    packet = _workstream(registry, packet_target())
    assert packet["status"] == "paused"
    assert packet["authorization_evidence"] == _rel(PACKET_LEAN_PACKET_PATH)
    assert packet["report"] == _rel(PACKET_OUT)
    assert packet["packet_result"] == PACKET_OUTCOME
    assert packet["strict_packet_result"] == PACKET_STRICT_OUTCOME
    assert packet["selected_next_target"] == consumed_target()

    review = _workstream(registry, consumed_target())
    assert review["status"] == "paused"
    assert review["authorization_evidence"] == evidence
    assert review["report"] == report
    assert review["prepared_packet_result"] == PACKET_OUTCOME
    assert review["prepared_packet_strict_result"] == PACKET_STRICT_OUTCOME
    assert review["review_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert review["psi_A_sourced_route_substituted"] == "no"
    assert review["proof_attempt_executed"] == "no"
    assert review["theorem_discharged"] == "no"
    assert review["rule_promoted"] == "no"
    assert review["master_action_promoted"] == "no"

    active = active_workstream(registry)
    if is_current:
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["report"] == report
        assert active["consumed_target"] == consumed_target()
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["attempt_preparation_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
        assert active["psi_A_sourced_route_substituted"] == "no"
        assert active["C_source_A_discharged"] == "no"
        assert active["sourced_maxwell_closure_claimed"] == "no"
        assert active["full_maxwell_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        attempt = _workstream(registry, NEXT_TARGET)
        assert attempt["status"] == "paused"
        assert attempt["attempt_preparation_result"] == (
            ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
        )
        assert attempt["selected_next_target"] == LIKELY_POST_ATTEMPT_REVIEW_TARGET
        assert attempt["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
        assert attempt["psi_A_sourced_route_substituted"] == "no"
        assert attempt["C_source_A_discharged"] == "no"
        assert active["workstream_id"] == LIKELY_POST_ATTEMPT_REVIEW_TARGET


def test_A_source_packet_result_review_mirrors() -> None:
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
        "ASourceTheoremLinkageObligationPacketResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_POST_ATTEMPT_REVIEW_TARGET,
        ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
        STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
        C_SOURCE_A_SHORT_FORM,
        SOURCE_ADMISSIBILITY_CONDITION,
        PSI_A_SOURCED_MAXWELL_ROUTE,
        PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
        LEAN_STATUS_WORDING_FOR_PACKET,
        "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_OUTCOME_v0",
        "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "standalone A-sector",
        "later psi-A sourced Maxwell route",
        "no theorem discharge during review",
        "no A-sector closure",
        "no sourced Maxwell closure by substitution",
        "no full Maxwell closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_A_source_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_A_source_theorem_linkage_obligation_packet_result_review_gate.py"
    )
