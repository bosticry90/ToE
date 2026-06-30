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
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_report import (
    BOUNDARY_ITEMS,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
    DEFAULT_OUT,
    FIELD_EULER_LAGRANGE_EQUATION,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LINKAGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_CONDITION,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PREPARED_LINKAGE_TARGET,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID,
    STANDALONE_PHI_SOURCE_ROUTE,
    STRESS_DIVERGENCE_TARGET,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    STRICT_SUGGESTED_REVIEW_OUTCOME,
    SUGGESTED_REVIEW_OUTCOME,
    TARGET_CONCLUSION,
    WATCH_ITEMS,
    build_phi_source_theorem_linkage_attempt_from_standalone_phi_route,
)
from formal.python.tools.phi_source_theorem_linkage_obligation_packet_result_review_report import (
    DEFAULT_OUT as REVIEW_OUT,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review_report import (
    DEFAULT_OUT as ATTEMPT_REVIEW_OUT,
    LEAN_PACKET_PATH as ATTEMPT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as PHI_ATTEMPT_EXECUTION_TARGET,
    OUTCOME_ID as PHI_ATTEMPT_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as STRICT_PHI_ATTEMPT_REVIEW_OUTCOME,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_report import (
    DEFAULT_OUT as PHI_ATTEMPT_EXECUTION_OUT,
    LEAN_PACKET_PATH as PHI_ATTEMPT_EXECUTION_LEAN_PACKET_PATH,
    NEXT_TARGET as PHI_ATTEMPT_EXECUTION_REVIEW_TARGET,
    OUTCOME_ID as PHI_ATTEMPT_EXECUTION_OUTCOME,
    STRICT_EXECUTION_RESULT as STRICT_PHI_ATTEMPT_EXECUTION_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_source_theorem_linkage_attempt_from_standalone_phi_route_report.py"
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
    return "prepare_phi_source_theorem_linkage_attempt_from_standalone_phi_route"


def test_phi_source_standalone_attempt_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_source_standalone_attempt_prepares_indexed_route() -> None:
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
    assert packet["watch_items"] == WATCH_ITEMS
    assert packet["boundary_items"] == BOUNDARY_ITEMS
    assert build_phi_source_theorem_linkage_attempt_from_standalone_phi_route() == packet


def test_phi_source_standalone_attempt_preserves_on_shell_scalar_route() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["standalone_phi_source_route"] == STANDALONE_PHI_SOURCE_ROUTE
    assert packet["standalone_phi_source_route_preserved"] is True
    assert packet["C_source_phi_residual_definition"] == C_SOURCE_PHI_RESIDUAL_DEFINITION
    assert packet["C_source_phi_source_admissibility_condition"] == (
        C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
    )
    assert packet["C_source_phi_target_statement"] == TARGET_CONCLUSION
    assert packet["source_admissibility_condition"] == TARGET_CONCLUSION
    assert packet["stress_divergence_target"] == STRESS_DIVERGENCE_TARGET
    assert packet["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert packet["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert packet["on_shell_condition"] == ON_SHELL_CONDITION
    assert packet["field_euler_lagrange_equation"] == FIELD_EULER_LAGRANGE_EQUATION
    assert packet["route_bundle_admissibility_form"] == ROUTE_BUNDLE_ADMISSIBILITY_FORM
    assert packet["target_conclusion"] == TARGET_CONCLUSION
    assert packet["prepared_linkage_target"] == PREPARED_LINKAGE_TARGET
    assert packet["linkage_route"] == LINKAGE_ROUTE
    assert packet["plain_meaning"] == PLAIN_MEANING
    assert packet["route_kind"] == "standalone_phi_on_shell_scalar_residual"


def test_phi_source_standalone_attempt_blocks_execution_and_route_contamination() -> None:
    packet = _json(DEFAULT_OUT)
    route_text = " ".join(packet["linkage_route"])

    assert packet["same_T_phi_definition"] is True
    assert packet["same_phi_sector_route"] is True
    assert packet["same_scalar_on_shell_assumptions"] is True
    assert packet["same_covariant_derivative_convention"] is True
    assert packet["same_sign_and_index_conventions"] is True
    assert packet["same_domain_and_boundary_assumptions"] is True
    assert packet["A_source_route_imported"] is False
    assert packet["A_sector_route_imported"] is False
    assert packet["psi_A_sourced_Maxwell_imported"] is False
    assert packet["psi_A_sourced_route_imported"] is False
    assert packet["QFT_GR_source_route_imported"] is False
    assert packet["J_current_imported"] is False
    assert "J^alpha" not in route_text
    assert "nabla_mu F" not in route_text
    assert "QFT-GR" not in route_text
    assert "do not replace the phi residual identity" in packet[
        "route_contamination_guard"
    ]
    assert packet["old_omnibus_tests_historical_hard_coded"] is True
    assert packet["old_omnibus_tests_not_active_acceptance_authority"] is True
    assert packet["silent_validation_downgrade_blocked"] is True

    for flag in [
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_execution_authorized",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_source_phi_discharged",
        "C_source_phi_linkage_constructed",
        "C_source_phi_zero_derived",
        "phi_source_theorem_linkage_obligation_discharged",
        "gap_1_through_gap_8_discharged",
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
    assert (
        packet["full_toeformal_aggregate_status_for_packet"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert packet["scoped_lean_targets_status_for_packet"] == "PASSED_SERIAL_RERUN"
    assert packet["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(packet)


def test_phi_source_standalone_attempt_rotates_to_result_review() -> None:
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
        registry, "review_phi_source_theorem_linkage_obligation_packet_result"
    )
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
    assert consumed["C_source_phi_residual_definition"] == (
        C_SOURCE_PHI_RESIDUAL_DEFINITION
    )
    assert consumed["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert consumed["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert consumed["theorem_discharged"] == "no"
    assert consumed["C_source_phi_discharged"] == "no"
    assert consumed["A_source_route_imported"] == "no"
    assert consumed["psi_A_sourced_Maxwell_imported"] == "no"
    assert consumed["QFT_GR_source_route_imported"] == "no"
    assert consumed["old_omnibus_tests_not_active_acceptance_authority"] == "yes"
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
        assert active["C_source_phi_residual_definition"] == (
            C_SOURCE_PHI_RESIDUAL_DEFINITION
        )
        assert active["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
        assert active["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
        assert active["proof_attempt_executed"] == "no"
        assert active["theorem_discharged"] == "no"
        assert active["C_source_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["old_omnibus_tests_not_active_acceptance_authority"] == "yes"
        assert active["master_action_promoted"] == "no"
        return

    review = _workstream(registry, NEXT_TARGET)
    assert review["status"] == "paused"
    assert review["authorization_evidence"] == _rel(ATTEMPT_REVIEW_LEAN_PACKET_PATH)
    assert review["report"] == _rel(ATTEMPT_REVIEW_OUT)
    assert review["attempt_preparation_result"] == OUTCOME_ID
    assert review["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert review["review_result"] == PHI_ATTEMPT_REVIEW_OUTCOME
    assert review["strict_review_result"] == STRICT_PHI_ATTEMPT_REVIEW_OUTCOME
    assert review["selected_next_target"] == PHI_ATTEMPT_EXECUTION_TARGET
    assert review["proof_attempt_executed"] == "no"
    assert review["theorem_discharged"] == "no"
    assert review["C_source_phi_discharged"] == "no"
    assert review["A_source_route_imported"] == "no"
    assert review["psi_A_sourced_Maxwell_imported"] == "no"
    assert review["QFT_GR_source_route_imported"] == "no"
    assert review["rule_promoted"] == "no"
    assert review["master_action_promoted"] == "no"

    if active["workstream_id"] == PHI_ATTEMPT_EXECUTION_TARGET:
        assert active["status"] == "active"
        assert active["consumed_target"] == NEXT_TARGET
        assert active["review_result"] == PHI_ATTEMPT_REVIEW_OUTCOME
        assert active["strict_review_result"] == STRICT_PHI_ATTEMPT_REVIEW_OUTCOME
        assert active["execution_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["proof_attempt_executed"] == "no"
        assert active["theorem_discharged"] == "no"
        assert active["C_source_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"
        return

    execution = _workstream(registry, PHI_ATTEMPT_EXECUTION_TARGET)
    assert execution["status"] == "paused"
    assert execution["authorization_evidence"] == (
        _rel(PHI_ATTEMPT_EXECUTION_LEAN_PACKET_PATH)
    )
    assert execution["report"] == _rel(PHI_ATTEMPT_EXECUTION_OUT)
    assert execution["execution_result"] == PHI_ATTEMPT_EXECUTION_OUTCOME
    assert execution["strict_execution_result"] == STRICT_PHI_ATTEMPT_EXECUTION_OUTCOME
    assert execution["selected_next_target"] == PHI_ATTEMPT_EXECUTION_REVIEW_TARGET
    assert execution["C_source_phi_zero_derived"] == "yes"
    assert execution["C_source_phi_discharged"] == "yes"
    assert execution["phi_sector_closure_claimed"] == "no"
    assert execution["master_action_promoted"] == "no"

    assert active["status"] == "active"
    assert active["workstream_id"] == PHI_ATTEMPT_EXECUTION_REVIEW_TARGET
    assert active["consumed_target"] == PHI_ATTEMPT_EXECUTION_TARGET
    assert active["execution_result"] == PHI_ATTEMPT_EXECUTION_OUTCOME
    assert active["strict_execution_result"] == STRICT_PHI_ATTEMPT_EXECUTION_OUTCOME
    assert active["review_result"] == "PENDING"
    assert active["selected_next_target"] == "PENDING"
    assert active["C_source_phi_zero_derived"] == "yes"
    assert active["C_source_phi_discharged"] == "yes"
    assert active["phi_sector_closure_claimed"] == "no"
    assert active["master_action_promoted"] == "no"


def test_phi_source_standalone_attempt_mirrors() -> None:
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
        "PhiSourceTheoremLinkageAttemptFromStandalonePhiRoute",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_REVIEW_OUTCOME,
        STRICT_SUGGESTED_REVIEW_OUTCOME,
        C_SOURCE_PHI_RESIDUAL_DEFINITION,
        RESIDUAL_IDENTITY_FORM,
        ON_SHELL_RESIDUAL_FORM,
        ON_SHELL_CONDITION,
        TARGET_CONCLUSION,
        LEAN_STATUS_WORDING_FOR_PACKET,
        "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_OUTCOME_v0",
        "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_NONCLAIM_BOUNDARY_v0",
        "old omnibus tests historical/hard-coded only",
        "old omnibus tests are not active-lane acceptance authority",
        "no theorem discharge during preparation",
        "no phi-sector closure",
        "no full scalar/QFT closure",
        "no QFT-GR closure",
        "no EM-QFT closure",
        "no general C_k closure",
        "no action embedding",
        "no variation",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_phi_source_standalone_attempt_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_theorem_linkage_attempt_from_standalone_phi_route_gate.py"
    )
