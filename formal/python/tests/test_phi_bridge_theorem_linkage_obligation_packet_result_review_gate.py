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
from formal.python.tools.phi_bridge_theorem_linkage_obligation_packet_report import (
    DEFAULT_OUT as PACKET_OUT,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    STRICT_PACKET_RESULT as PACKET_STRICT_OUTCOME,
)
from formal.python.tools.phi_bridge_theorem_linkage_obligation_packet_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    LIKELY_COMPONENTWISE_ATTEMPT_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    ROUTE_PURITY_WATCH_ITEMS,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    STANDALONE_PHI_BRIDGE_ROUTE,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_PREPARATION_OUTCOME,
    SUGGESTED_PREPARATION_OUTCOME,
    build_phi_bridge_theorem_linkage_obligation_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_bridge_theorem_linkage_obligation_packet_result_review_report.py"
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
    return "review_phi_bridge_theorem_linkage_obligation_packet_result"


def packet_target() -> str:
    return "prepare_phi_bridge_theorem_linkage_obligation_packet"


def test_phi_bridge_packet_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_bridge_packet_result_review_accepts_packet_scope() -> None:
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
    assert review["suggested_preparation_outcome"] == SUGGESTED_PREPARATION_OUTCOME
    assert review["strict_suggested_preparation_outcome"] == (
        STRICT_SUGGESTED_PREPARATION_OUTCOME
    )
    assert review["prepared_packet_result"] == PACKET_OUTCOME
    assert review["prepared_packet_strict_result"] == PACKET_STRICT_OUTCOME
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["route_purity_watch_items"] == ROUTE_PURITY_WATCH_ITEMS
    assert build_phi_bridge_theorem_linkage_obligation_packet_result_review() == review


def test_phi_bridge_packet_result_review_preserves_bridge_registry_route() -> None:
    review = _json(DEFAULT_OUT)

    assert review["standalone_phi_bridge_route"] == STANDALONE_PHI_BRIDGE_ROUTE
    assert review["standalone_phi_bridge_route_preserved"] is True
    assert review["exact_tuple_definition_preserved"] is True
    assert review["target_C_bridge_phi_zero_preserved"] is True
    assert review["bridge_candidate_id"] == BRIDGE_CANDIDATE_ID
    assert review["bridge_candidate_type"] == BRIDGE_CANDIDATE_TYPE
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["bridge_route_field_equation_match"] == (
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH
    )
    assert review["bridge_route_stress_energy_match"] == (
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH
    )
    assert review["bridge_route_source_residual_match"] == (
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
    )
    assert review["bridge_candidate_rule_plain_meaning"] == (
        BRIDGE_CANDIDATE_RULE_PLAIN_MEANING
    )
    assert review["bridge_route_alignment_sequence"] == BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
    assert review["bridge_route_alignment_sequence_plain"] == (
        BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN
    )
    assert review["source_rule_closeout_outcome"] == SOURCE_RULE_CLOSEOUT_OUTCOME
    assert review["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert review["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert review["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert review["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["likely_componentwise_attempt_route"] == (
        LIKELY_COMPONENTWISE_ATTEMPT_ROUTE
    )
    assert review["master_witness_route_match_target_indexed"] is True


def test_phi_bridge_packet_result_review_blocks_execution_and_route_substitution() -> None:
    review = _json(DEFAULT_OUT)

    assert review["C_source_phi_route_reused"] is False
    assert review["C_bridge_phi_route_reused_from_C_source_phi"] is False
    assert review["A_source_route_imported"] is False
    assert review["A_sector_route_imported"] is False
    assert review["psi_A_route_imported"] is False
    assert review["psi_A_sourced_route_imported"] is False
    assert review["psi_A_sourced_Maxwell_imported"] is False
    assert review["QFT_GR_route_imported"] is False
    assert review["QFT_GR_source_route_imported"] is False
    assert review["master_action_route_substituted"] is False
    assert "do not substitute C_source^phi" in review["route_contamination_guard"]
    assert "A-source" in review["route_contamination_guard"]
    assert "psi-A" in review["route_contamination_guard"]
    assert "QFT-GR" in review["route_contamination_guard"]
    assert "master-action routes" in review["route_contamination_guard"]
    assert "master-action promotion" in review["master_action_promotion_watch"]

    for flag in [
        "review_executes_proof",
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_execution_authorized",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_bridge_phi_discharged",
        "C_bridge_phi_theorem_linkage_gap_discharged",
        "C_bridge_phi_theorem_linkage_obligation_discharged",
        "C_bridge_phi_proof_executed",
        "bridge_admissibility_proved",
        "bridge_route_alignment_verified",
        "route_consistency_tuple_proved",
        "field_equation_match_proved",
        "stress_energy_match_proved",
        "source_residual_match_proved",
        "general_C_k_closure",
        "C_k_dynamical_law_status",
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

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_PACKET
    assert review["lean_status_wording_lines"] == LEAN_STATUS_WORDING_LINES_FOR_PACKET
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert review["scoped_lean_targets_status_for_review"] == "PASSED_SERIAL_RERUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_phi_bridge_packet_result_review_rotates_to_attempt_preparation() -> None:
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
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
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
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["report"] == report
        assert active["consumed_target"] == consumed_target()
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["attempt_preparation_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
        assert active["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
        assert active["bridge_route_field_equation_match"] == (
            BRIDGE_ROUTE_FIELD_EQUATION_MATCH
        )
        assert active["bridge_route_stress_energy_match"] == (
            BRIDGE_ROUTE_STRESS_ENERGY_MATCH
        )
        assert active["bridge_route_source_residual_match"] == (
            BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        )
        assert active["proof_attempt_executed"] == "no"
        assert active["C_bridge_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"


def test_phi_bridge_packet_result_review_mirrors() -> None:
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
        "PhiBridgeTheoremLinkageObligationPacketResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_PREPARATION_OUTCOME,
        STRICT_SUGGESTED_PREPARATION_OUTCOME,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        *LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_OUTCOME_v0",
        "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "do not let master/witness route match become master-action promotion",
        "local C_bridge^phi theorem-linkage obligation only",
        "no C_source^phi route substitution",
        "no A-source route substitution",
        "no psi-A route substitution",
        "no QFT-GR route substitution",
        "no proof execution during review",
        "no C_bridge^phi discharge during review",
        "no phi-sector closure",
        "no scalar/QFT closure",
        "no QFT-GR closure",
        "no EM-QFT closure",
        "no seam closure",
        "no general C_k closure",
        "no C_k promotion",
        "no action embedding",
        "no variation",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_phi_bridge_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_bridge_theorem_linkage_obligation_packet_result_review_gate.py"
    )
