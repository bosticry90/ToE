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
from formal.python.tools.phi_transport_theorem_linkage_obligation_packet_report import (
    DEFAULT_OUT as PACKET_OUT,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    STRICT_PACKET_RESULT as PACKET_STRICT_OUTCOME,
)
from formal.python.tools.phi_transport_theorem_linkage_obligation_packet_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_RULE_CLOSEOUT_OUTCOME,
    COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
    DEFAULT_OUT,
    EXACT_PRIOR_TRANSPORT_ADMISSIBILITY_TARGET,
    EXACT_PRIOR_TRANSPORT_STATEMENT,
    EXACT_PRIOR_TRANSPORT_TARGET,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    LIKELY_COMPONENTWISE_ATTEMPT_ROUTE,
    LIKELY_PLAIN_MEANING,
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
    STANDALONE_PHI_TRANSPORT_ROUTE,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_ATTEMPT_PREPARATION_OUTCOME,
    SUGGESTED_ATTEMPT_PREPARATION_OUTCOME,
    TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_CLOSEOUT_RULE_ROLE,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RULE_CLASSIFICATION,
    TRANSPORT_RULE_EPISTEMIC_STATUS,
    build_phi_transport_theorem_linkage_obligation_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_transport_theorem_linkage_obligation_packet_result_review_report.py"
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
    return "review_phi_transport_theorem_linkage_obligation_packet_result"


def packet_target() -> str:
    return "prepare_phi_transport_theorem_linkage_obligation_packet"


def test_phi_transport_packet_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_transport_packet_result_review_accepts_packet_scope() -> None:
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
    assert (
        review["suggested_attempt_preparation_outcome"]
        == SUGGESTED_ATTEMPT_PREPARATION_OUTCOME
    )
    assert review["strict_suggested_attempt_preparation_outcome"] == (
        STRICT_SUGGESTED_ATTEMPT_PREPARATION_OUTCOME
    )
    assert review["prepared_packet_result"] == PACKET_OUTCOME
    assert review["prepared_packet_strict_result"] == PACKET_STRICT_OUTCOME
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["route_purity_watch_items"] == ROUTE_PURITY_WATCH_ITEMS
    assert build_phi_transport_theorem_linkage_obligation_packet_result_review() == review


def test_phi_transport_packet_result_review_preserves_transport_registry_route() -> None:
    review = _json(DEFAULT_OUT)

    assert review["standalone_phi_transport_route"] == STANDALONE_PHI_TRANSPORT_ROUTE
    assert review["standalone_phi_transport_route_preserved"] is True
    assert review["exact_five_component_transport_tuple_preserved"] is True
    assert review["target_C_transport_phi_zero_preserved"] is True
    assert review["exact_prior_transport_statement_frozen"] is True
    assert review["exact_prior_transport_target_frozen"] is True
    assert review["exact_prior_transport_statement"] == EXACT_PRIOR_TRANSPORT_STATEMENT
    assert review["exact_prior_transport_target"] == EXACT_PRIOR_TRANSPORT_TARGET
    assert review["exact_prior_transport_admissibility_target"] == (
        EXACT_PRIOR_TRANSPORT_ADMISSIBILITY_TARGET
    )
    assert review["transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert review["transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert review["transport_rule_classification"] == TRANSPORT_RULE_CLASSIFICATION
    assert review["transport_closeout_rule_classification"] == (
        TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
    )
    assert review["transport_rule_role"] == TRANSPORT_CLOSEOUT_RULE_ROLE
    assert review["transport_rule_epistemic_status"] == TRANSPORT_RULE_EPISTEMIC_STATUS
    assert review["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert review["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert review["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["transport_component_count"] == len(TRANSPORT_COMPONENTS)
    assert review["transport_component_forms"] == [
        row["component_form"] for row in TRANSPORT_COMPONENTS
    ]
    assert review["transport_action_variation_component_preserved"] is True
    assert review["transport_variation_bridge_component_preserved"] is True
    assert review["transport_bridge_source_component_preserved"] is True
    assert review["transport_source_residual_component_preserved"] is True
    assert review["transport_residual_regime_component_preserved"] is True
    assert review["transport_action_embedding_chain_form"] == (
        TRANSPORT_ACTION_EMBEDDING_CHAIN_FORM
    )
    assert review["known_phi_transport_chain_form"] == KNOWN_PHI_TRANSPORT_CHAIN_FORM
    assert review["likely_plain_meaning"] == LIKELY_PLAIN_MEANING
    assert review["likely_componentwise_attempt_route"] == (
        LIKELY_COMPONENTWISE_ATTEMPT_ROUTE
    )


def test_phi_transport_packet_result_review_preserves_prior_context() -> None:
    review = _json(DEFAULT_OUT)

    assert review["source_rule_closeout_outcome"] == SOURCE_RULE_CLOSEOUT_OUTCOME
    assert review["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert review["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert review["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert review["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["bridge_rule_closeout_outcome"] == BRIDGE_RULE_CLOSEOUT_OUTCOME
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["completed_local_theorem_linkage_chain"] == (
        COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
    )


def test_phi_transport_packet_result_review_blocks_execution_and_substitution() -> None:
    review = _json(DEFAULT_OUT)

    assert review["C_source_phi_route_reused"] is False
    assert review["C_bridge_phi_route_reused"] is False
    assert review["C_bridge_phi_route_reused_as_transport"] is False
    assert review["A_source_route_imported"] is False
    assert review["A_sector_route_imported"] is False
    assert review["psi_A_route_imported"] is False
    assert review["psi_A_sourced_route_imported"] is False
    assert review["psi_A_sourced_Maxwell_imported"] is False
    assert review["QFT_GR_route_imported"] is False
    assert review["QFT_GR_source_route_imported"] is False
    assert review["master_action_route_substituted"] is False
    assert "do not substitute C_source^phi" in review["route_contamination_guard"]
    assert "C_bridge^phi" in review["route_contamination_guard"]
    assert "A-sector" in review["route_contamination_guard"]
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
        "C_transport_phi_discharged",
        "C_transport_phi_theorem_linkage_gap_discharged",
        "C_transport_phi_theorem_linkage_obligation_discharged",
        "C_transport_phi_proof_executed",
        "C_transport_phi_closure_claimed",
        "transport_consistency_proved",
        "transport_components_proved",
        "transport_candidate_rule_proved",
        "full_route_alignment_proved",
        "route_chain_compatibility_proved",
        "source_admissibility_proved",
        "bridge_admissibility_proved",
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


def test_phi_transport_packet_result_review_rotates_to_attempt_preparation() -> None:
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
    assert review["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert review["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert review["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["new_transport_formula_invented"] == "no"
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
        assert active["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
        assert active["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
        assert active["transport_admissibility_constraint_form"] == (
            TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
        )
        assert active["likely_componentwise_attempt_route"] == "; ".join(
            LIKELY_COMPONENTWISE_ATTEMPT_ROUTE
        )
        assert active["proof_attempt_executed"] == "no"
        assert active["C_transport_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"


def test_phi_transport_packet_result_review_mirrors() -> None:
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
        "PhiTransportTheoremLinkageObligationPacketResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_ATTEMPT_PREPARATION_OUTCOME,
        STRICT_SUGGESTED_ATTEMPT_PREPARATION_OUTCOME,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        KNOWN_PHI_TRANSPORT_CHAIN_FORM,
        TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
        TRANSPORT_CLOSEOUT_RULE_ROLE,
        LIKELY_PLAIN_MEANING,
        *[row["component_form"] for row in TRANSPORT_COMPONENTS],
        *LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_OUTCOME_v0",
        "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "exact five-component transport tuple preserved",
        "ACTION -> VARIATION transport component preserved",
        "VARIATION -> BRIDGE transport component preserved",
        "BRIDGE -> SOURCE transport component preserved",
        "SOURCE -> RESIDUAL transport component preserved",
        "RESIDUAL -> REGIME transport component preserved",
        "no proof execution",
        "no theorem discharge",
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


def test_phi_transport_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_transport_theorem_linkage_obligation_packet_result_review_gate.py"
    )
