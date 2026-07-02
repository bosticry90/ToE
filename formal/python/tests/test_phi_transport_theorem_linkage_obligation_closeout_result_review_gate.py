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
from formal.python.tools.phi_transport_theorem_linkage_obligation_closeout_report import (
    DEFAULT_OUT as CLOSEOUT_PATH,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    OUTCOME_ID as CLOSEOUT_RESULT,
    STRICT_CLOSEOUT_RESULT,
)
from formal.python.tools.phi_transport_theorem_linkage_obligation_closeout_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    COMPLETED_LOCAL_PHI_THEOREM_LINKAGE_CHAIN,
    CONSUMED_TARGET,
    COMPONENTWISE_ZERO_ROUTE,
    C_TRANSPORT_TUPLE_ZERO,
    DEFAULT_OUT,
    DISCIPLINED_NEXT_STEP,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
    LIKELY_SELECTOR_FOLLOW_ON_TARGET,
    LOCAL_CLOSEOUT_ROUTE,
    LOCAL_CLOSEOUT_ROUTE_TEXT,
    NEXT_STEP_REASON,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REVIEW_RESULT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTOR_QUESTION,
    STRICT_REVIEW_RESULT,
    TARGET_CONCLUSION,
    TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
    TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
    TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
    build_phi_transport_theorem_linkage_obligation_closeout_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_transport_theorem_linkage_obligation_closeout_result_review_report.py"
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
    rows = [
        row
        for row in payload["workstreams"]
        if row.get("workstream_id") == workstream_id
    ]
    assert rows, f"Missing workstream: {workstream_id}"
    return rows[-1]


def test_phi_transport_closeout_result_review_files_exist() -> None:
    for path in [
        CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        CLOSEOUT_LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_transport_closeout_result_review_accepts_local_closeout() -> None:
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
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selector_question"] == SELECTOR_QUESTION
    assert review["likely_selector_follow_on_target"] == LIKELY_SELECTOR_FOLLOW_ON_TARGET
    assert review["disciplined_next_step"] == DISCIPLINED_NEXT_STEP
    assert review["next_step_reason"] == NEXT_STEP_REASON
    assert (
        build_phi_transport_theorem_linkage_obligation_closeout_result_review()
        == review
    )


def test_phi_transport_closeout_result_review_preserves_route_and_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["closeout_outcome"] == CLOSEOUT_RESULT
    assert review["closeout_strict_outcome"] == STRICT_CLOSEOUT_RESULT
    assert review["closeout_claims"] == CLOSEOUT_CLAIMS
    assert review["nonclaims"] == NONCLAIMS
    assert review["claim_boundary"] == CLAIM_BOUNDARY
    assert review["completed_local_phi_theorem_linkage_chain"] == (
        COMPLETED_LOCAL_PHI_THEOREM_LINKAGE_CHAIN
    )
    assert review["C_source_phi_locally_linked"] is True
    assert review["C_bridge_phi_locally_linked"] is True
    assert review["C_transport_phi_locally_linked"] is True
    assert review["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert review["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert review["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert review["transport_action_variation_zero_component"] == (
        TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT
    )
    assert review["transport_variation_bridge_zero_component"] == (
        TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT
    )
    assert review["transport_bridge_source_zero_component"] == (
        TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT
    )
    assert review["transport_source_residual_zero_component"] == (
        TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT
    )
    assert review["transport_residual_regime_zero_component"] == (
        TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT
    )
    assert review["C_transport_tuple_zero"] == C_TRANSPORT_TUPLE_ZERO
    assert review["target_conclusion"] == TARGET_CONCLUSION
    assert review["local_closeout_route"] == LOCAL_CLOSEOUT_ROUTE
    assert review["local_closeout_route_text"] == LOCAL_CLOSEOUT_ROUTE_TEXT
    assert review["componentwise_zero_route"] == COMPONENTWISE_ZERO_ROUTE
    assert review["phi_transport_closeout_result_review_accepted"] is True
    assert review["phi_transport_theorem_linkage_obligation_closeout_accepted"] is True
    assert review["phi_transport_theorem_linkage_obligation_locally_closed"] is True
    assert review["five_component_C_transport_phi_tuple_preserved"] is True
    assert review["transport_action_variation_zero_component_preserved"] is True
    assert review["transport_variation_bridge_zero_component_preserved"] is True
    assert review["transport_bridge_source_zero_component_preserved"] is True
    assert review["transport_source_residual_zero_component_preserved"] is True
    assert review["transport_residual_regime_zero_component_preserved"] is True
    assert review["C_transport_phi_zero_locally_linked"] is True
    assert review["C_transport_phi_zero_constructed"] is True
    assert review["C_transport_phi_zero_derived"] is True
    assert review["C_transport_phi_linkage_constructed"] is True
    assert review["selector_authorized"] is True
    assert review["selector_executed"] is False
    assert review["next_theorem_linkage_obligation_selected"] is False
    assert review["review_executes_new_proof"] is False
    assert review["proof_execution_authorized"] is False

    for key in [
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
        "J_current_imported",
        "C_transport_phi_closure_claimed",
        "phi_sector_closure_claimed",
        "full_scalar_qft_closure_claimed",
        "full_scalar_QFT_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "general_C_k_closure",
        "general_C_k_theorem_linkage_closure",
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


def test_phi_transport_closeout_result_review_records_lean_status() -> None:
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


def test_phi_transport_closeout_result_review_rotates_to_selector() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    report = _rel(DEFAULT_OUT)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["closeout_result"] == CLOSEOUT_RESULT
    assert consumed["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["selector_authorized"] == "yes"
    assert consumed["selector_executed"] == "no"
    assert consumed["next_theorem_linkage_obligation_selected"] == "no"
    assert consumed["C_transport_phi_zero_locally_linked"] == "yes"
    assert consumed["C_transport_phi_zero_derived"] == "yes"
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
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["report"] == report
        assert active["consumed_target"] == CONSUMED_TARGET
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["selection_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["selector_question"] == SELECTOR_QUESTION
        assert active["likely_selector_follow_on_target"] == (
            LIKELY_SELECTOR_FOLLOW_ON_TARGET
        )
        assert active["selector_authorized"] == "yes"
        assert active["selector_executed"] == "no"
        assert active["proof_attempt_executed"] == "no"
        assert active["theorem_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["em_qft_closure_claimed"] == "no"
        assert active["seam_closure_claim"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]


def test_phi_transport_closeout_result_review_mirrors() -> None:
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
        "PhiTransportTheoremLinkageObligationCloseoutResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SELECTOR_QUESTION,
        DISCIPLINED_NEXT_STEP,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
        TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
        TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
        TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
        TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
        C_TRANSPORT_TUPLE_ZERO,
        TARGET_CONCLUSION,
        *LOCAL_CLOSEOUT_ROUTE,
        LEAN_STATUS_WORDING_FOR_REVIEW.replace("\n", "; "),
        "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "phi-transport theorem-linkage obligation closeout accepted",
        "five-component C_transport^phi tuple preserved",
        "ACTION -> VARIATION zero component preserved",
        "VARIATION -> BRIDGE zero component preserved",
        "BRIDGE -> SOURCE zero component preserved",
        "SOURCE -> RESIDUAL zero component preserved",
        "RESIDUAL -> REGIME zero component preserved",
        "C_transport^phi = 0 locally constructed, reviewed, and closed",
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


def test_phi_transport_closeout_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_transport_theorem_linkage_obligation_closeout_result_review_gate.py"
    )
