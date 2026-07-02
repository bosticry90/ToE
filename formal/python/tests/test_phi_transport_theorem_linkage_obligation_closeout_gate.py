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
    CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    COMPONENTWISE_ZERO_ROUTE,
    CONSUMED_TARGET,
    C_TRANSPORT_TUPLE_ZERO,
    DEFAULT_OUT,
    EXECUTED_COMPONENTWISE_ROUTE,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LEAN_STATUS_WORDING_LINES_FOR_CLOSEOUT,
    LOCAL_CLOSEOUT_ROUTE,
    LOCAL_CLOSEOUT_ROUTE_TEXT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    STRICT_CLOSEOUT_RESULT,
    STRICT_SUGGESTED_REVIEW_OUTCOME,
    SUGGESTED_REVIEW_OUTCOME,
    TARGET_CONCLUSION,
    TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT,
    TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT,
    TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT,
    build_phi_transport_theorem_linkage_obligation_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_transport_theorem_linkage_obligation_closeout_report.py"
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


def _workstreams(target: str, registry: dict, *, status: str | None = None) -> list[dict]:
    rows = [
        row
        for row in registry["workstreams"]
        if row.get("workstream_id") == target
        and (status is None or row.get("status") == status)
    ]
    assert rows, f"missing workstream {target!r} with status {status!r}"
    return rows


def test_phi_transport_closeout_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_transport_closeout_accepts_local_route() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["artifact_id"] == SCHEMA_ID
    assert closeout["schema_id"] == SCHEMA_ID
    assert closeout["packet_id"] == PACKET_ID
    assert closeout["prepared"] is True
    assert closeout["accepted"] is True
    assert closeout["closed"] is True
    assert closeout["outcome_id"] == OUTCOME_ID
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["packet_result"] == OUTCOME_ID
    assert closeout["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert closeout["packet_classification"] == PACKET_CLASSIFICATION
    assert closeout["consumed_target"] == CONSUMED_TARGET
    assert closeout["selected_next_target"] == NEXT_TARGET
    assert closeout["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert closeout["suggested_review_outcome"] == SUGGESTED_REVIEW_OUTCOME
    assert closeout["strict_suggested_review_outcome"] == (
        STRICT_SUGGESTED_REVIEW_OUTCOME
    )
    assert closeout["closeout_statement"] == CLOSEOUT_STATEMENT
    assert build_phi_transport_theorem_linkage_obligation_closeout() == closeout


def test_phi_transport_closeout_records_claims_and_nonclaims() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["closeout_claims"] == CLOSEOUT_CLAIMS
    assert closeout["nonclaims"] == NONCLAIMS
    assert closeout["claim_boundary"] == CLAIM_BOUNDARY
    assert closeout["transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert closeout["transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert closeout["transport_admissibility_constraint_form"] == (
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert closeout["transport_action_variation_zero_component"] == (
        TRANSPORT_ACTION_VARIATION_ZERO_COMPONENT
    )
    assert closeout["transport_variation_bridge_zero_component"] == (
        TRANSPORT_VARIATION_BRIDGE_ZERO_COMPONENT
    )
    assert closeout["transport_bridge_source_zero_component"] == (
        TRANSPORT_BRIDGE_SOURCE_ZERO_COMPONENT
    )
    assert closeout["transport_source_residual_zero_component"] == (
        TRANSPORT_SOURCE_RESIDUAL_ZERO_COMPONENT
    )
    assert closeout["transport_residual_regime_zero_component"] == (
        TRANSPORT_RESIDUAL_REGIME_ZERO_COMPONENT
    )
    assert closeout["C_transport_tuple_zero"] == C_TRANSPORT_TUPLE_ZERO
    assert closeout["target_conclusion"] == TARGET_CONCLUSION
    assert closeout["componentwise_zero_route"] == COMPONENTWISE_ZERO_ROUTE
    assert closeout["executed_componentwise_route"] == EXECUTED_COMPONENTWISE_ROUTE
    assert closeout["local_closeout_route"] == LOCAL_CLOSEOUT_ROUTE
    assert closeout["local_closeout_route_text"] == LOCAL_CLOSEOUT_ROUTE_TEXT
    assert closeout["linkage_route"] == LOCAL_CLOSEOUT_ROUTE
    assert closeout["local_phi_transport_theorem_linkage_obligation_closed"] is True
    assert closeout["phi_transport_theorem_linkage_obligation_locally_closed"] is True
    assert closeout["five_component_C_transport_phi_tuple_preserved"] is True
    assert closeout["transport_action_variation_zero_component_preserved"] is True
    assert closeout["transport_variation_bridge_zero_component_preserved"] is True
    assert closeout["transport_bridge_source_zero_component_preserved"] is True
    assert closeout["transport_source_residual_zero_component_preserved"] is True
    assert closeout["transport_residual_regime_zero_component_preserved"] is True
    assert closeout["componentwise_zero_route_reviewed"] is True
    assert closeout["C_transport_phi_zero_constructed"] is True
    assert closeout["C_transport_phi_zero_derived"] is True
    assert closeout["C_transport_phi_linkage_constructed"] is True
    assert closeout["constructed_and_reviewed"] is True
    assert closeout["closeout_executes_new_proof"] is False
    assert closeout["proof_execution_authorized"] is False

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
        assert closeout[key] is False, key


def test_phi_transport_closeout_records_lean_status() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_CLOSEOUT
    assert closeout["lean_status_wording_lines"] == LEAN_STATUS_WORDING_LINES_FOR_CLOSEOUT
    assert (
        closeout["full_toeformal_aggregate_status_for_closeout"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT
    )
    assert (
        closeout["scoped_lean_targets_status_for_closeout"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT
    )
    assert closeout["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(closeout)


def test_phi_transport_closeout_rotates_to_result_review() -> None:
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

    consumed = _workstreams(CONSUMED_TARGET, registry, status="paused")[-1]
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["phi_transport_theorem_linkage_obligation_locally_closed"] == "yes"
    assert consumed["five_component_C_transport_phi_tuple_preserved"] == "yes"
    assert consumed["componentwise_zero_route_reviewed"] == "yes"
    assert consumed["C_transport_phi_zero_constructed"] == "yes"
    assert consumed["C_transport_phi_zero_derived"] == "yes"
    assert consumed["phi_sector_closure_claimed"] == "no"
    assert consumed["full_scalar_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["em_qft_closure_claimed"] == "no"
    assert consumed["general_C_k_closure"] == "no"
    assert consumed["seam_closure_claim"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        assert NEXT_TARGET not in registry["paused_lanes"]
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["report"] == report
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["consumed_target"] == CONSUMED_TARGET
        assert active["closeout_result"] == OUTCOME_ID
        assert active["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
        assert active["review_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["phi_transport_theorem_linkage_obligation_locally_closed"] == "yes"
        assert active["five_component_C_transport_phi_tuple_preserved"] == "yes"
        assert active["componentwise_zero_route_reviewed"] == "yes"
        assert active["C_transport_phi_zero_constructed"] == "yes"
        assert active["C_transport_phi_zero_derived"] == "yes"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["em_qft_closure_claimed"] == "no"
        assert active["general_C_k_closure"] == "no"
        assert active["seam_closure_claim"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]


def test_phi_transport_closeout_mirrors() -> None:
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
        STRICT_CLOSEOUT_RESULT,
        PACKET_CLASSIFICATION,
        "PhiTransportTheoremLinkageObligationCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_REVIEW_OUTCOME,
        STRICT_SUGGESTED_REVIEW_OUTCOME,
        CLOSEOUT_STATEMENT,
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
        LEAN_STATUS_WORDING_FOR_CLOSEOUT.replace("\n", "; "),
        "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_OUTCOME_v0",
        "PHI_TRANSPORT_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "phi-transport theorem-linkage obligation locally closed",
        "five-component C_transport^phi tuple preserved",
        "ACTION -> VARIATION zero component preserved",
        "VARIATION -> BRIDGE zero component preserved",
        "BRIDGE -> SOURCE zero component preserved",
        "SOURCE -> RESIDUAL zero component preserved",
        "RESIDUAL -> REGIME zero component preserved",
        "componentwise zero route reviewed",
        "C_transport^phi = 0 locally constructed and ready for closeout",
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


def test_phi_transport_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_transport_theorem_linkage_obligation_closeout_gate.py"
    )
