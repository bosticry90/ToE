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
from formal.python.tools.phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_report import (
    BOUNDARY_ITEMS,
    COMPONENTWISE_ZERO_ROUTE,
    C_TRANSPORT_TUPLE_ZERO,
    DEFAULT_OUT,
    KNOWN_PHI_TRANSPORT_CHAIN_FORM,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PREPARATION_CLAIMS,
    PREPARED_LINKAGE_TARGET,
    SCHEMA_ID,
    STANDALONE_PHI_TRANSPORT_ROUTE,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    STRICT_SUGGESTED_REVIEW_OUTCOME,
    SUGGESTED_REVIEW_OUTCOME,
    TARGET_CONCLUSION,
    TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
    TRANSPORT_COMPONENTS,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
    TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
    TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
    WATCH_ITEMS,
    build_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route,
)
from formal.python.tools.phi_transport_theorem_linkage_obligation_packet_result_review_report import (
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
    / "phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_report.py"
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
    return "prepare_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route"


def review_target() -> str:
    return "review_phi_transport_theorem_linkage_obligation_packet_result"


def test_phi_transport_standalone_attempt_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_transport_standalone_attempt_prepares_componentwise_zero_route() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["attempt_prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["attempt_preparation_result"] == OUTCOME_ID
    assert packet["packet_result"] == OUTCOME_ID
    assert packet["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == consumed_target()
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["suggested_review_outcome"] == SUGGESTED_REVIEW_OUTCOME
    assert packet["strict_suggested_review_outcome"] == (
        STRICT_SUGGESTED_REVIEW_OUTCOME
    )
    assert packet["preparation_claims"] == PREPARATION_CLAIMS
    assert packet["watch_items"] == WATCH_ITEMS
    assert packet["boundary_items"] == BOUNDARY_ITEMS
    assert (
        build_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route()
        == packet
    )


def test_phi_transport_standalone_attempt_preserves_transport_tuple_and_components() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["standalone_phi_transport_route"] == STANDALONE_PHI_TRANSPORT_ROUTE
    assert packet["standalone_phi_transport_route_preserved"] is True
    assert packet["exact_five_component_transport_tuple_preserved"] is True
    assert packet["target_C_transport_phi_zero_preserved"] is True
    assert packet["componentwise_zero_target_prepared"] is True
    assert packet["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert packet["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert packet["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["transport_component_count"] == len(TRANSPORT_COMPONENTS)
    assert packet["transport_component_forms"] == [
        row["component_form"] for row in TRANSPORT_COMPONENTS
    ]
    assert packet["transport_action_variation_zero_component"] == (
        TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT
    )
    assert packet["transport_variation_bridge_zero_component"] == (
        TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT
    )
    assert packet["transport_bridge_source_zero_component"] == (
        TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT
    )
    assert packet["transport_source_residual_zero_component"] == (
        TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT
    )
    assert packet["transport_residual_regime_zero_component"] == (
        TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT
    )
    assert packet["componentwise_zero_route"] == COMPONENTWISE_ZERO_ROUTE
    assert packet["C_transport_tuple_zero"] == C_TRANSPORT_TUPLE_ZERO
    assert packet["target_conclusion"] == TARGET_CONCLUSION
    assert packet["prepared_linkage_target"] == PREPARED_LINKAGE_TARGET
    assert packet["plain_meaning"] == PLAIN_MEANING
    assert packet["known_phi_transport_chain_form"] == KNOWN_PHI_TRANSPORT_CHAIN_FORM
    assert (
        packet["route_kind"]
        == "standalone_phi_transport_componentwise_zero_preparation"
    )


def test_phi_transport_standalone_attempt_blocks_execution_and_substitution() -> None:
    packet = _json(DEFAULT_OUT)
    route_text = " ".join(packet["componentwise_zero_route"])

    assert packet["componentwise_transport_zero_route_indexed"] is True
    assert packet["action_to_regime_transport_match_target_prepared"] is True
    assert packet["action_to_regime_transport_match_promoted_to_master_action"] is False
    assert packet["same_standalone_phi_transport_registry_tuple"] is True
    assert packet["same_action_variation_component"] is True
    assert packet["same_variation_bridge_component"] is True
    assert packet["same_bridge_source_component"] is True
    assert packet["same_source_residual_component"] is True
    assert packet["same_residual_regime_component"] is True
    assert packet["same_component_order"] is True
    assert "C_source^phi =" not in route_text
    assert "C_bridge^phi =" not in route_text
    assert "J^alpha" not in route_text
    assert "nabla_mu F" not in route_text
    assert "QFT-GR" not in route_text
    assert "C_source^phi" in packet["route_contamination_guard"]
    assert "C_bridge^phi" in packet["route_contamination_guard"]
    assert "master-action promotion" in packet["route_contamination_guard"]

    for flag in [
        "preparation_executes_proof",
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_execution_authorized",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_transport_phi_discharged",
        "C_transport_phi_zero_derived",
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
        "gap_1_through_gap_8_discharged",
        "new_transport_formula_invented",
        "C_source_phi_route_reused",
        "C_bridge_phi_route_reused",
        "C_bridge_phi_route_reused_as_transport",
        "A_source_route_imported",
        "A_sector_route_imported",
        "psi_A_route_imported",
        "psi_A_sourced_Maxwell_imported",
        "QFT_GR_route_imported",
        "QFT_GR_source_route_imported",
        "master_action_route_substituted",
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
        assert packet[flag] is False, flag

    assert packet["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_PACKET
    assert packet["lean_status_wording_lines"] == LEAN_STATUS_WORDING_LINES_FOR_PACKET
    assert (
        packet["full_toeformal_aggregate_status_for_packet"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert packet["scoped_lean_targets_status_for_packet"] == "PASSED_SERIAL_RERUN"
    assert packet["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(packet)


def test_phi_transport_standalone_attempt_rotates_to_result_review() -> None:
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

    prior_review = _workstream(registry, review_target())
    assert prior_review["status"] == "paused"
    assert prior_review["authorization_evidence"] == _rel(REVIEW_LEAN_PACKET_PATH)
    assert prior_review["report"] == _rel(REVIEW_OUT)
    assert prior_review["review_result"] == REVIEW_OUTCOME
    assert prior_review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert prior_review["selected_next_target"] == consumed_target()

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["attempt_preparation_result"] == OUTCOME_ID
    assert consumed["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert consumed["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert consumed["componentwise_zero_route"] == "; ".join(COMPONENTWISE_ZERO_ROUTE)
    assert consumed["C_transport_phi_discharged"] == "no"
    assert consumed["theorem_discharged"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = active_workstream(registry)
    if is_current:
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["report"] == report
        assert active["consumed_target"] == consumed_target()
        assert active["attempt_preparation_result"] == OUTCOME_ID
        assert active["review_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["componentwise_zero_route"] == "; ".join(COMPONENTWISE_ZERO_ROUTE)
        assert active["C_transport_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"


def test_phi_transport_standalone_attempt_mirrors() -> None:
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
        "PhiTransportTheoremLinkageAttemptFromStandalonePhiTransportRoute",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_REVIEW_OUTCOME,
        STRICT_SUGGESTED_REVIEW_OUTCOME,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        *[row["component_form"] for row in TRANSPORT_COMPONENTS],
        C_TRANSPORT_TUPLE_ZERO,
        TARGET_CONCLUSION,
        *LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_OUTCOME_v0",
        "PHI_TRANSPORT_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_TRANSPORT_ROUTE_NONCLAIM_BOUNDARY_v0",
        "phi-transport theorem-linkage attempt prepared",
        "five-component transport route preserved",
        "ACTION -> VARIATION component indexed",
        "VARIATION -> BRIDGE component indexed",
        "BRIDGE -> SOURCE component indexed",
        "SOURCE -> RESIDUAL component indexed",
        "RESIDUAL -> REGIME component indexed",
        "componentwise zero target prepared",
        "no proof execution during preparation",
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


def test_phi_transport_standalone_attempt_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_transport_theorem_linkage_attempt_from_standalone_phi_transport_route_gate.py"
    )
