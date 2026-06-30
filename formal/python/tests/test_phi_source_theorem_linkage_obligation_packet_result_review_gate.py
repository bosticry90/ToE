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
from formal.python.tools.phi_source_theorem_linkage_obligation_packet_report import (
    DEFAULT_OUT as PACKET_OUT,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    STRICT_PACKET_RESULT as PACKET_STRICT_OUTCOME,
)
from formal.python.tools.phi_source_theorem_linkage_obligation_packet_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
    DEFAULT_OUT,
    FIELD_EULER_LAGRANGE_EQUATION,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    ROUTE_PURITY_WATCH_ITEMS,
    SCHEMA_ID,
    STANDALONE_PHI_SOURCE_ROUTE,
    STRESS_DIVERGENCE_TARGET,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_PREPARATION_OUTCOME,
    SUGGESTED_PREPARATION_OUTCOME,
    build_phi_source_theorem_linkage_obligation_packet_result_review,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_report import (
    NEXT_TARGET as PHI_ATTEMPT_REVIEW_TARGET,
    OUTCOME_ID as PHI_ATTEMPT_OUTCOME,
    STRICT_ATTEMPT_PREPARATION_RESULT as STRICT_PHI_ATTEMPT_OUTCOME,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review_report import (
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
    / "phi_source_theorem_linkage_obligation_packet_result_review_report.py"
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
    return "review_phi_source_theorem_linkage_obligation_packet_result"


def packet_target() -> str:
    return "prepare_phi_source_theorem_linkage_obligation_packet"


def test_phi_source_packet_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_source_packet_result_review_accepts_packet_scope() -> None:
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
    assert build_phi_source_theorem_linkage_obligation_packet_result_review() == review


def test_phi_source_packet_result_review_preserves_phi_registry_route() -> None:
    review = _json(DEFAULT_OUT)

    assert review["standalone_phi_source_route"] == STANDALONE_PHI_SOURCE_ROUTE
    assert review["standalone_phi_source_route_preserved"] is True
    assert review["C_source_phi_residual_definition"] == C_SOURCE_PHI_RESIDUAL_DEFINITION
    assert review["C_source_phi_source_admissibility_condition"] == (
        C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
    )
    assert review["C_source_phi_target_statement"] == (
        C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
    )
    assert review["source_admissibility_condition"] == (
        C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
    )
    assert review["stress_divergence_target"] == STRESS_DIVERGENCE_TARGET
    assert review["exact_registry_statement_frozen"] is True
    assert review["scalar_on_shell_residual_identity_preserved"] is True
    assert review["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert review["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert review["on_shell_implication_form"] == ON_SHELL_IMPLICATION_FORM
    assert review["route_bundle_admissibility_form"] == ROUTE_BUNDLE_ADMISSIBILITY_FORM
    assert review["field_euler_lagrange_equation"] == FIELD_EULER_LAGRANGE_EQUATION
    assert review["stress_energy_under_selected_policy"] == (
        STRESS_ENERGY_UNDER_SELECTED_POLICY
    )


def test_phi_source_packet_result_review_blocks_execution_and_route_contamination() -> None:
    review = _json(DEFAULT_OUT)

    assert review["same_T_phi_definition"] is True
    assert review["same_phi_sector_route"] is True
    assert review["same_scalar_on_shell_assumptions"] is True
    assert review["same_covariant_derivative_convention"] is True
    assert review["same_sign_and_index_conventions"] is True
    assert review["same_domain_and_boundary_assumptions"] is True
    assert review["A_source_route_imported"] is False
    assert review["A_sector_route_imported"] is False
    assert review["psi_A_sourced_Maxwell_imported"] is False
    assert review["psi_A_sourced_route_imported"] is False
    assert review["QFT_GR_source_route_imported"] is False
    assert "do not import A-sector" in review["route_contamination_guard"]
    assert "psi-A sourced Maxwell" in review["route_contamination_guard"]
    assert "QFT-GR source routes" in review["route_contamination_guard"]
    assert "do not replace the scalar/on-shell residual identity" in review[
        "route_contamination_guard"
    ]

    for flag in [
        "review_executes_proof",
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_execution_authorized",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_source_phi_discharged",
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
        assert review[flag] is False, flag

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_PACKET
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert review["scoped_lean_targets_status_for_review"] == "PASSED_SERIAL_RERUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_phi_source_packet_result_review_rotates_to_attempt_preparation() -> None:
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
    assert review["C_source_phi_residual_definition"] == (
        C_SOURCE_PHI_RESIDUAL_DEFINITION
    )
    assert review["source_admissibility_condition"] == (
        C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
    )
    assert review["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert review["A_source_route_imported"] == "no"
    assert review["psi_A_sourced_Maxwell_imported"] == "no"
    assert review["QFT_GR_source_route_imported"] == "no"
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
        assert active["C_source_phi_residual_definition"] == (
            C_SOURCE_PHI_RESIDUAL_DEFINITION
        )
        assert active["source_admissibility_condition"] == (
            C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
        )
        assert active["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
        assert active["A_source_route_imported"] == "no"
        assert active["psi_A_sourced_Maxwell_imported"] == "no"
        assert active["QFT_GR_source_route_imported"] == "no"
        assert active["proof_attempt_executed"] == "no"
        assert active["C_source_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"
        return

    attempt = _workstream(registry, NEXT_TARGET)
    assert attempt["status"] == "paused"
    assert attempt["attempt_preparation_result"] == PHI_ATTEMPT_OUTCOME
    assert attempt["strict_attempt_preparation_result"] == STRICT_PHI_ATTEMPT_OUTCOME
    assert attempt["selected_next_target"] == PHI_ATTEMPT_REVIEW_TARGET
    assert attempt["proof_attempt_executed"] == "no"
    assert attempt["theorem_discharged"] == "no"
    assert attempt["C_source_phi_discharged"] == "no"
    assert attempt["A_source_route_imported"] == "no"
    assert attempt["psi_A_sourced_Maxwell_imported"] == "no"
    assert attempt["QFT_GR_source_route_imported"] == "no"
    assert attempt["rule_promoted"] == "no"
    assert attempt["master_action_promoted"] == "no"

    if active["workstream_id"] == PHI_ATTEMPT_REVIEW_TARGET:
        assert active["status"] == "active"
        assert active["consumed_target"] == NEXT_TARGET
        assert active["attempt_preparation_result"] == PHI_ATTEMPT_OUTCOME
        assert active["strict_attempt_preparation_result"] == STRICT_PHI_ATTEMPT_OUTCOME
        assert active["review_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["proof_attempt_executed"] == "no"
        assert active["theorem_discharged"] == "no"
        assert active["C_source_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"
        return

    attempt_review = _workstream(registry, PHI_ATTEMPT_REVIEW_TARGET)
    assert attempt_review["status"] == "paused"
    assert attempt_review["review_result"] == PHI_ATTEMPT_REVIEW_OUTCOME
    assert attempt_review["strict_review_result"] == STRICT_PHI_ATTEMPT_REVIEW_OUTCOME
    assert attempt_review["selected_next_target"] == PHI_ATTEMPT_EXECUTION_TARGET
    assert attempt_review["proof_attempt_executed"] == "no"
    assert attempt_review["theorem_discharged"] == "no"
    assert attempt_review["C_source_phi_discharged"] == "no"
    assert attempt_review["A_source_route_imported"] == "no"
    assert attempt_review["psi_A_sourced_Maxwell_imported"] == "no"
    assert attempt_review["QFT_GR_source_route_imported"] == "no"
    assert attempt_review["rule_promoted"] == "no"
    assert attempt_review["master_action_promoted"] == "no"

    if active["workstream_id"] == PHI_ATTEMPT_EXECUTION_TARGET:
        assert active["status"] == "active"
        assert active["consumed_target"] == PHI_ATTEMPT_REVIEW_TARGET
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


def test_phi_source_packet_result_review_mirrors() -> None:
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
        "PhiSourceTheoremLinkageObligationPacketResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_PREPARATION_OUTCOME,
        STRICT_SUGGESTED_PREPARATION_OUTCOME,
        C_SOURCE_PHI_RESIDUAL_DEFINITION,
        C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
        ON_SHELL_RESIDUAL_FORM,
        RESIDUAL_IDENTITY_FORM,
        ON_SHELL_IMPLICATION_FORM,
        LEAN_STATUS_WORDING_FOR_PACKET,
        "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_OUTCOME_v0",
        "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "no A-sector route import",
        "no psi-A sourced Maxwell import",
        "no QFT-GR source-route import",
        "no silent replacement of the phi residual identity",
        "no proof execution during review",
        "no C_source^phi discharge during review",
        "no phi-sector closure",
        "no full scalar/QFT closure",
        "no QFT-GR or EM-QFT closure",
        "no general C_k closure",
        "no action embedding",
        "no variation",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_phi_source_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_theorem_linkage_obligation_packet_result_review_gate.py"
    )
