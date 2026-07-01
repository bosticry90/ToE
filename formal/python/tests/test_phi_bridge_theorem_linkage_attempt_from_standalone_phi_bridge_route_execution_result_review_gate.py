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
from formal.python.tools.phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_report import (
    DEFAULT_OUT as EXECUTION_OUT,
    LEAN_PACKET_PATH as EXECUTION_LEAN_PACKET_PATH,
    OUTCOME_ID as EXECUTION_OUTCOME,
    STRICT_EXECUTION_RESULT,
)
from formal.python.tools.phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_TUPLE_ZERO,
    CLOSEOUT_OUTCOME,
    CLOSEOUT_STATEMENT,
    COMPONENTWISE_ZERO_ROUTE,
    DEFAULT_OUT,
    EXECUTED_COMPONENTWISE_ROUTE,
    EXECUTION_ROUTE_TO_AUTHORIZE,
    FIELD_EQUATION_MATCH,
    FIELD_EQUATION_ZERO_COMPONENT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
    MAIN_BOUNDARY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    REVIEW_RESULT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SOURCE_RESIDUAL_MATCH,
    SOURCE_RESIDUAL_ZERO_COMPONENT,
    STRESS_ENERGY_MATCH,
    STRESS_ENERGY_ZERO_COMPONENT,
    STRICT_CLOSEOUT_OUTCOME,
    STRICT_REVIEW_RESULT,
    TARGET_CONCLUSION,
    build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review_report.py"
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
    return "review_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result"


def test_phi_bridge_execution_result_review_files_exist() -> None:
    for path in [
        EXECUTION_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        EXECUTION_LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_bridge_execution_result_review_accepts_local_linkage() -> None:
    review = _json(DEFAULT_OUT)

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["reviewed"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == consumed_target()
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["closeout_outcome"] == CLOSEOUT_OUTCOME
    assert review["strict_closeout_outcome"] == STRICT_CLOSEOUT_OUTCOME
    assert review["closeout_statement"] == CLOSEOUT_STATEMENT
    assert (
        build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review()
        == review
    )


def test_phi_bridge_execution_result_review_records_route_and_boundaries() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["bridge_constraint_form"] == BRIDGE_CONSTRAINT_FORM
    assert review["bridge_constraint_equation"] == BRIDGE_CONSTRAINT_EQUATION
    assert review["field_equation_match"] == FIELD_EQUATION_MATCH
    assert review["stress_energy_match"] == STRESS_ENERGY_MATCH
    assert review["source_residual_match"] == SOURCE_RESIDUAL_MATCH
    assert review["field_equation_zero_component"] == FIELD_EQUATION_ZERO_COMPONENT
    assert review["stress_energy_zero_component"] == STRESS_ENERGY_ZERO_COMPONENT
    assert review["source_residual_zero_component"] == SOURCE_RESIDUAL_ZERO_COMPONENT
    assert review["bridge_tuple_zero"] == BRIDGE_TUPLE_ZERO
    assert review["target_conclusion"] == TARGET_CONCLUSION
    assert review["componentwise_zero_route"] == COMPONENTWISE_ZERO_ROUTE
    assert review["executed_componentwise_route"] == EXECUTED_COMPONENTWISE_ROUTE
    assert review["execution_route_to_authorize"] == EXECUTION_ROUTE_TO_AUTHORIZE
    assert review["plain_meaning"] == PLAIN_MEANING
    assert review["main_boundary"] == MAIN_BOUNDARY
    assert review["exact_tuple_definition_preserved"] is True
    assert review["E_phi_master_witness_equality_preserved"] is True
    assert review["T_phi_master_witness_equality_preserved"] is True
    assert review["C_source_phi_divergence_match_equality_preserved"] is True
    assert review["componentwise_zero_route_constructed"] is True
    assert review["C_bridge_phi_zero_derived"] is True
    assert review["C_bridge_phi_linkage_constructed"] is True
    assert review["lean_execution_marker_preserved"] is True
    assert review["json_execution_report_preserved"] is True
    assert review["focused_execution_gates_passed"] is True
    assert review["review_executes_attempt"] is False
    assert review["proof_execution_authorized"] is False
    assert review["proof_attempt_executed"] is True
    assert review["theorem_discharged"] is True
    assert review["closeout_preparation_authorized"] is True

    for key in [
        "C_source_phi_route_reused",
        "C_bridge_phi_route_reused_from_C_source_phi",
        "A_source_route_imported",
        "A_sector_route_imported",
        "psi_A_route_imported",
        "psi_A_sourced_Maxwell_imported",
        "QFT_GR_route_imported",
        "QFT_GR_source_route_imported",
        "master_action_route_substituted",
        "new_bridge_formula_invented",
        "bridge_admissibility_proved",
        "field_equation_match_proved",
        "stress_energy_match_proved",
        "source_residual_match_proved",
        "C_bridge_phi_closure_claimed",
        "phi_sector_closure_claimed",
        "full_scalar_qft_closure_claimed",
        "full_scalar_QFT_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "general_C_k_closure",
        "rule_promoted",
        "C_k_rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "action_embedding_claimed",
        "action_variation_executed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_phi_bridge_execution_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_REVIEW
    assert review["lean_status_wording_lines"] == LEAN_STATUS_WORDING_LINES_FOR_REVIEW
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
    )
    assert (
        review["scoped_lean_targets_status_for_review"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
    )
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_phi_bridge_execution_result_review_rotates_to_closeout_preparation() -> None:
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

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["execution_result"] == EXECUTION_OUTCOME
    assert consumed["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["C_bridge_phi_zero_derived"] == "yes"
    assert consumed["phi_sector_closure_claimed"] == "no"
    assert consumed["full_scalar_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["seam_closure_claim"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["report"] == report
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["consumed_target"] == consumed_target()
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["closeout_outcome_suggested"] == CLOSEOUT_OUTCOME
        assert active["strict_closeout_outcome_suggested"] == STRICT_CLOSEOUT_OUTCOME
        assert active["closeout_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["C_bridge_phi_zero_derived"] == "yes"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["em_qft_closure_claimed"] == "no"
        assert active["general_C_k_closure"] == "no"
        assert active["seam_closure_claim"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"


def test_phi_bridge_execution_result_review_mirrors() -> None:
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
        "PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRouteExecutionResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        CLOSEOUT_OUTCOME,
        STRICT_CLOSEOUT_OUTCOME,
        CLOSEOUT_STATEMENT,
        BRIDGE_CONSTRAINT_FORM,
        BRIDGE_CONSTRAINT_EQUATION,
        FIELD_EQUATION_MATCH,
        STRESS_ENERGY_MATCH,
        SOURCE_RESIDUAL_MATCH,
        BRIDGE_TUPLE_ZERO,
        TARGET_CONCLUSION,
        MAIN_BOUNDARY,
        *LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
        "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_EXECUTION_RESULT_REVIEW_OUTCOME_v0",
        "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_EXECUTION_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "phi-bridge theorem-linkage execution accepted",
        "C_bridge^phi tuple definition preserved",
        "E_phi master/witness equality preserved",
        "T_phi master/witness equality preserved",
        "C_source^phi divergence-match equality preserved",
        "componentwise zero route constructed",
        "C_bridge^phi = 0 locally constructed",
        "Lean execution marker preserved",
        "JSON execution report preserved",
        "focused execution gates passed",
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


def test_phi_bridge_execution_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_execution_result_review_gate.py"
    )
