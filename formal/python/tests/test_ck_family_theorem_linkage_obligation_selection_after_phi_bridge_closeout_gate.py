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
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_report import (
    AVOIDED_CLAIMS,
    BLOCKED_CLAIMS,
    COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FOLLOW_ON_TARGET_AFTER_REVIEW,
    FORBIDDEN_REUSED_ROUTES,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_SELECTION,
    LEAN_STATUS_WORDING_LINES_FOR_SELECTION,
    MAIN_WATCH_ITEM,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_TRANSPORT_REGISTRY_BOUNDARY,
    PLAIN_MEANING,
    ROUTE_BOUNDARY,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_ROW_ID,
    SELECTED_THEOREM_LINKAGE_GAP,
    STRICT_SELECTION_RESULT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    build_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_report.py"
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


def test_ck_family_selection_after_phi_bridge_closeout_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_selection_after_phi_bridge_closeout_selects_C_transport_phi() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["artifact_id"] == SCHEMA_ID
    assert selection["schema_id"] == SCHEMA_ID
    assert selection["packet_id"] == PACKET_ID
    assert selection["prepared"] is True
    assert selection["accepted"] is True
    assert selection["selected"] is True
    assert selection["outcome_id"] == OUTCOME_ID
    assert selection["selection_result"] == OUTCOME_ID
    assert selection["selector_outcome"] == OUTCOME_ID
    assert selection["packet_result"] == OUTCOME_ID
    assert selection["strict_selection_result"] == STRICT_SELECTION_RESULT
    assert selection["strict_selector_outcome"] == STRICT_SELECTION_RESULT
    assert selection["packet_classification"] == PACKET_CLASSIFICATION
    assert selection["selected_obligation"] == SELECTED_OBLIGATION
    assert selection["selected_theorem_linkage_gap"] == SELECTED_THEOREM_LINKAGE_GAP
    assert selection["selected_obligation_row_id"] == SELECTED_OBLIGATION_ROW_ID
    assert selection["selected_next_target"] == NEXT_TARGET
    assert selection["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert selection["follow_on_target_after_review"] == FOLLOW_ON_TARGET_AFTER_REVIEW
    assert (
        selection["completed_local_theorem_linkage_chain"]
        == COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
    )
    assert (
        build_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout()
        == selection
    )


def test_ck_family_selection_after_phi_bridge_closeout_preserves_transport_registry_boundary() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["plain_meaning"] == PLAIN_MEANING
    assert selection["route_boundary"] == ROUTE_BOUNDARY
    assert selection["main_watch_item"] == MAIN_WATCH_ITEM
    assert selection["phi_transport_registry_boundary"] == PHI_TRANSPORT_REGISTRY_BOUNDARY
    assert selection["prior_phi_transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert selection["prior_phi_transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert selection["prior_phi_transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert (
        selection["prior_phi_transport_constraint_equation"]
        == TRANSPORT_CONSTRAINT_EQUATION
    )
    assert (
        selection["prior_phi_transport_admissibility_constraint_form"]
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert selection["forbidden_reused_routes"] == FORBIDDEN_REUSED_ROUTES
    assert selection["avoided_claims"] == AVOIDED_CLAIMS
    assert selection["blocked_claims"] == BLOCKED_CLAIMS
    assert selection["selector_only"] is True
    assert selection["C_transport_phi_route_recovered_from_prior_registry"] is True

    for key in [
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "gap_discharged",
        "C_transport_phi_theorem_linkage_gap_discharged",
        "C_transport_phi_theorem_linkage_obligation_discharged",
        "C_transport_phi_proof_executed",
        "C_transport_phi_closure_claimed",
        "rule_promoted",
        "C_source_phi_route_reused",
        "C_bridge_phi_route_reused",
        "C_bridge_phi_route_reused_as_transport",
        "A_source_route_imported",
        "A_sector_route_imported",
        "psi_A_route_imported",
        "psi_A_sourced_route_imported",
        "QFT_GR_route_imported",
        "QFT_GR_source_route_imported",
        "phi_sector_closure_claimed",
        "full_scalar_qft_closure_claimed",
        "A_sector_closure_claimed",
        "sourced_maxwell_closure_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "general_C_k_closure",
        "action_embedding_claimed",
        "action_variation_executed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert selection[key] is False, key


def test_ck_family_selection_after_phi_bridge_closeout_records_lean_status() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_SELECTION
    assert selection["lean_status_wording_lines"] == LEAN_STATUS_WORDING_LINES_FOR_SELECTION
    assert (
        selection["full_toeformal_aggregate_status_for_selection"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION
    )
    assert (
        selection["scoped_lean_targets_status_for_selection"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION
    )
    assert selection["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(selection)


def test_ck_family_selection_after_phi_bridge_closeout_rotates_to_review() -> None:
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
    assert FOLLOW_ON_TARGET_AFTER_REVIEW in registry["next_strict_target_coverage"]

    selector = _workstream(registry, CONSUMED_TARGET)
    assert selector["status"] == "paused"
    assert selector["authorization_evidence"] == evidence
    assert selector["report"] == report
    assert selector["selector_outcome"] == OUTCOME_ID
    assert selector["strict_selector_outcome"] == STRICT_SELECTION_RESULT
    assert selector["selected_next_target"] == NEXT_TARGET
    assert selector["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert selector["follow_on_target_after_review"] == FOLLOW_ON_TARGET_AFTER_REVIEW
    assert selector["selected_obligation"] == SELECTED_OBLIGATION
    assert selector["selected_obligation_row_id"] == SELECTED_OBLIGATION_ROW_ID
    assert selector["main_watch_item"] == MAIN_WATCH_ITEM
    assert selector["proof_execution_authorized"] == "no"
    assert selector["gap_discharged"] == "no"
    assert selector["phi_sector_closure_claimed"] == "no"
    assert selector["C_source_phi_route_reused"] == "no"
    assert selector["C_bridge_phi_route_reused"] == "no"
    assert selector["A_sector_route_imported"] == "no"
    assert selector["psi_A_route_imported"] == "no"
    assert selector["QFT_GR_route_imported"] == "no"
    assert selector["rule_promoted"] == "no"
    assert selector["master_action_promoted"] == "no"

    if is_current:
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["report"] == report
        assert active["consumed_target"] == CONSUMED_TARGET
        assert active["selector_outcome"] == OUTCOME_ID
        assert active["strict_selector_outcome"] == STRICT_SELECTION_RESULT
        assert active["review_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["selected_obligation"] == SELECTED_OBLIGATION
        assert active["follow_on_target_after_review"] == FOLLOW_ON_TARGET_AFTER_REVIEW
        assert active["main_watch_item"] == MAIN_WATCH_ITEM
        assert active["proof_execution_authorized"] == "no"
        assert active["gap_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["C_source_phi_route_reused"] == "no"
        assert active["C_bridge_phi_route_reused"] == "no"
        assert active["A_sector_route_imported"] == "no"
        assert active["psi_A_route_imported"] == "no"
        assert active["QFT_GR_route_imported"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]


def test_ck_family_selection_after_phi_bridge_closeout_mirrors() -> None:
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
        STRICT_SELECTION_RESULT,
        PACKET_CLASSIFICATION,
        "CKFamilyTheoremLinkageObligationSelectionAfterPhiBridgeCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        FOLLOW_ON_TARGET_AFTER_REVIEW,
        SELECTED_OBLIGATION,
        SELECTED_THEOREM_LINKAGE_GAP,
        PHI_TRANSPORT_REGISTRY_BOUNDARY,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        ROUTE_BOUNDARY,
        MAIN_WATCH_ITEM,
        LEAN_STATUS_WORDING_LINES_FOR_SELECTION[0],
        LEAN_STATUS_WORDING_LINES_FOR_SELECTION[1],
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "do not execute the C_transport^phi proof route",
        "do not discharge the C_transport^phi theorem-linkage gap",
        "do not claim phi-sector closure",
        "do not reuse the C_source^phi theorem-linkage route as the transport route",
        "do not reuse the C_bridge^phi theorem-linkage route as the transport route",
        "do not import an A-sector route",
        "do not import a psi-A route",
        "do not import a QFT-GR route",
        "do not promote the master action",
    ]:
        assert token in joined, token


def test_ck_family_selection_after_phi_bridge_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_gate.py"
    )
