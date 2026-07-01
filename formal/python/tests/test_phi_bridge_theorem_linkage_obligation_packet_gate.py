from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_phi_source_closeout_result_review_report import (
    DEFAULT_OUT as SELECTOR_REVIEW_OUT,
    LEAN_PACKET_PATH as SELECTOR_REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as SELECTOR_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as SELECTOR_STRICT_REVIEW_OUTCOME,
)
from formal.python.tools.phi_bridge_theorem_linkage_obligation_packet_report import (
    BOUNDARY_ITEMS,
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
    COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_SCOPE_RECORD,
    RECOVERY_ITEMS,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_EQUATION,
    SOURCE_CANDIDATE_CONSTRAINT_FORM,
    SOURCE_CANDIDATE_CONSTRAINT_ID,
    SOURCE_RULE_CLOSEOUT_OUTCOME,
    STANDALONE_PHI_BRIDGE_ROUTE,
    STRICT_PACKET_RESULT,
    STRICT_SUGGESTED_REVIEW_OUTCOME,
    SUGGESTED_REVIEW_OUTCOME,
    WATCH_ITEMS,
    build_phi_bridge_theorem_linkage_obligation_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_bridge_theorem_linkage_obligation_packet_report.py"
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
    return "prepare_phi_bridge_theorem_linkage_obligation_packet"


def test_phi_bridge_theorem_linkage_obligation_packet_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_bridge_theorem_linkage_obligation_packet_scopes_prior_bridge_route() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["packet_prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == OUTCOME_ID
    assert packet["strict_packet_result"] == STRICT_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == consumed_target()
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["suggested_review_outcome"] == SUGGESTED_REVIEW_OUTCOME
    assert packet["strict_suggested_review_outcome"] == STRICT_SUGGESTED_REVIEW_OUTCOME
    assert packet["packet_scope_record"] == PACKET_SCOPE_RECORD
    assert packet["recovery_items"] == RECOVERY_ITEMS
    assert packet["watch_items"] == WATCH_ITEMS
    assert packet["boundary_items"] == BOUNDARY_ITEMS
    assert build_phi_bridge_theorem_linkage_obligation_packet() == packet


def test_phi_bridge_theorem_linkage_obligation_packet_freezes_registry_statement() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["standalone_phi_bridge_route"] == STANDALONE_PHI_BRIDGE_ROUTE
    assert packet["standalone_phi_bridge_route_recovered"] is True
    assert packet["standalone_phi_bridge_route_preserved"] is True
    assert packet["exact_prior_bridge_statement_frozen"] is True
    assert packet["exact_prior_bridge_target_frozen"] is True
    assert packet["exact_prior_bridge_statement"] == BRIDGE_CONSTRAINT_FORM
    assert packet["exact_prior_bridge_target"] == BRIDGE_CONSTRAINT_EQUATION
    assert packet["bridge_candidate_id"] == BRIDGE_CANDIDATE_ID
    assert packet["bridge_candidate_type"] == BRIDGE_CANDIDATE_TYPE
    assert packet["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert packet["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert packet["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["bridge_route_field_equation_match"] == (
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH
    )
    assert packet["bridge_route_stress_energy_match"] == (
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH
    )
    assert packet["bridge_route_source_residual_match"] == (
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
    )
    assert packet["bridge_candidate_rule_plain_meaning"] == (
        BRIDGE_CANDIDATE_RULE_PLAIN_MEANING
    )
    assert packet["likely_plain_meaning"] == BRIDGE_CANDIDATE_RULE_PLAIN_MEANING
    assert packet["bridge_route_alignment_sequence"] == BRIDGE_ROUTE_ALIGNMENT_SEQUENCE
    assert packet["bridge_route_alignment_sequence_plain"] == (
        BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN
    )
    assert packet["source_rule_closeout_outcome"] == SOURCE_RULE_CLOSEOUT_OUTCOME
    assert packet["source_candidate_constraint_id"] == SOURCE_CANDIDATE_CONSTRAINT_ID
    assert packet["source_candidate_constraint_form"] == SOURCE_CANDIDATE_CONSTRAINT_FORM
    assert packet["source_candidate_constraint_equation"] == (
        SOURCE_CANDIDATE_CONSTRAINT_EQUATION
    )
    assert packet["source_admissibility_constraint_form"] == (
        SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert packet["completed_local_theorem_linkage_chain"] == (
        COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
    )


def test_phi_bridge_theorem_linkage_obligation_packet_blocks_route_substitution() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["new_bridge_formula_invented"] is False
    assert packet["C_source_phi_route_reused"] is False
    assert packet["C_bridge_phi_route_reused_from_C_source_phi"] is False
    assert packet["A_source_route_imported"] is False
    assert packet["A_sector_route_imported"] is False
    assert packet["psi_A_route_imported"] is False
    assert packet["psi_A_sourced_route_imported"] is False
    assert packet["psi_A_sourced_Maxwell_imported"] is False
    assert packet["QFT_GR_route_imported"] is False
    assert packet["QFT_GR_source_route_imported"] is False
    assert packet["master_action_route_substituted"] is False
    assert "do not substitute C_source^phi" in packet["route_contamination_guard"]
    assert "A-source" in packet["route_contamination_guard"]
    assert "psi-A" in packet["route_contamination_guard"]
    assert "QFT-GR" in packet["route_contamination_guard"]
    assert "master-action routes" in packet["route_contamination_guard"]


def test_phi_bridge_theorem_linkage_obligation_packet_preserves_boundaries() -> None:
    packet = _json(DEFAULT_OUT)

    for flag in [
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


def test_phi_bridge_theorem_linkage_obligation_packet_rotates_to_review() -> None:
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

    prior_review = _workstream(
        registry,
        "review_ck_family_theorem_linkage_obligation_selection_after_phi_source_closeout_result",
    )
    assert prior_review["status"] == "paused"
    assert prior_review["authorization_evidence"] == _rel(
        SELECTOR_REVIEW_LEAN_PACKET_PATH
    )
    assert prior_review["report"] == _rel(SELECTOR_REVIEW_OUT)
    assert prior_review["review_result"] == SELECTOR_REVIEW_OUTCOME
    assert prior_review["strict_review_result"] == SELECTOR_STRICT_REVIEW_OUTCOME
    assert prior_review["selected_next_target"] == consumed_target()

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["strict_packet_result"] == STRICT_PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert consumed["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert consumed["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert consumed["new_bridge_formula_invented"] == "no"
    assert consumed["C_source_phi_route_reused"] == "no"
    assert consumed["A_source_route_imported"] == "no"
    assert consumed["psi_A_sourced_Maxwell_imported"] == "no"
    assert consumed["QFT_GR_source_route_imported"] == "no"
    assert consumed["proof_attempt_executed"] == "no"
    assert consumed["theorem_discharged"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    review_row = _workstream(registry, NEXT_TARGET)
    if is_current:
        assert review_row["status"] == "active"
        assert review_row["workstream_id"] == NEXT_TARGET
        assert review_row["active_lane"] == NEXT_TARGET
        assert review_row["authorization_evidence"] == evidence
        assert review_row["authorized_next_strict_target"] == NEXT_TARGET
        assert review_row["report"] == report
        assert review_row["consumed_target"] == consumed_target()
        assert review_row["packet_result"] == OUTCOME_ID
        assert review_row["strict_packet_result"] == STRICT_PACKET_RESULT
        assert review_row["review_result"] == "PENDING"
        assert review_row["selected_next_target"] == "PENDING"
    else:
        assert review_row["status"] == "paused"
    assert review_row["selected_obligation"] == "C_bridge^phi theorem-linkage obligation"
    assert review_row["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review_row["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review_row["bridge_admissibility_constraint_form"] == (
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review_row["new_bridge_formula_invented"] == "no"
    assert review_row["C_source_phi_route_reused"] == "no"
    assert review_row["A_source_route_imported"] == "no"
    assert review_row["psi_A_sourced_Maxwell_imported"] == "no"
    assert review_row["QFT_GR_source_route_imported"] == "no"
    assert review_row["proof_execution_authorized"] == "no"
    assert review_row["C_bridge_phi_discharged"] == "no"
    assert review_row["phi_sector_closure_claimed"] == "no"
    assert review_row["qft_gr_closure_claimed"] == "no"
    assert review_row["master_action_promoted"] == "no"


def test_phi_bridge_theorem_linkage_obligation_packet_mirrors() -> None:
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
        "PhiBridgeTheoremLinkageObligationPacket",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_OUTCOME_v0",
        "PHI_BRIDGE_THEOREM_LINKAGE_OBLIGATION_PACKET_NONCLAIM_BOUNDARY_v0",
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


def test_phi_bridge_theorem_linkage_obligation_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_bridge_theorem_linkage_obligation_packet_gate.py"
    )
