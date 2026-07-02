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
    DEFAULT_OUT as SELECTION_OUT,
    LEAN_PACKET_PATH as SELECTION_LEAN_PACKET_PATH,
    NEXT_TARGET as SELECTOR_REVIEW_TARGET,
    OUTCOME_ID as SELECTION_OUTCOME,
    STRICT_SELECTION_RESULT,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result_review_report import (
    BLOCKED_CLAIMS,
    COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN,
    DEFAULT_OUT,
    FORBIDDEN_REUSED_ROUTES,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
    LIKELY_PACKET_OUTCOME,
    LIKELY_POST_PACKET_REVIEW_TARGET,
    MAIN_WATCH_ITEM,
    NEXT_PACKET_RECOVERY_ITEMS,
    NEXT_PACKET_SCOPE_INSTRUCTION,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PHI_TRANSPORT_REGISTRY_BOUNDARY,
    REVIEW_ACCEPTANCE_SUMMARY,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_ROW_ID,
    SELECTED_THEOREM_LINKAGE_GAP,
    STRICT_LIKELY_PACKET_OUTCOME,
    STRICT_REVIEW_RESULT,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_CANDIDATE_ID,
    TRANSPORT_CANDIDATE_TYPE,
    TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION,
    TRANSPORT_CONSTRAINT_EQUATION,
    TRANSPORT_CONSTRAINT_FORM,
    build_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result_review_report.py"
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
    return SELECTOR_REVIEW_TARGET


def test_ck_family_selection_after_phi_bridge_closeout_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_selection_after_phi_bridge_closeout_result_review_accepts_transport_selection() -> None:
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
    assert review["likely_packet_outcome"] == LIKELY_PACKET_OUTCOME
    assert review["strict_likely_packet_outcome"] == STRICT_LIKELY_PACKET_OUTCOME
    assert review["selected_obligation"] == SELECTED_OBLIGATION
    assert review["selected_theorem_linkage_gap"] == SELECTED_THEOREM_LINKAGE_GAP
    assert review["selected_obligation_row_id"] == SELECTED_OBLIGATION_ROW_ID
    assert (
        review["completed_local_theorem_linkage_chain"]
        == COMPLETED_LOCAL_THEOREM_LINKAGE_CHAIN
    )
    assert review["review_acceptance_summary"] == REVIEW_ACCEPTANCE_SUMMARY
    assert (
        build_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result_review()
        == review
    )


def test_ck_family_selection_after_phi_bridge_closeout_result_review_preserves_transport_registry_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["next_packet_scope"] == NEXT_PACKET_SCOPE_INSTRUCTION
    assert review["next_packet_recovery_items"] == NEXT_PACKET_RECOVERY_ITEMS
    assert review["likely_post_packet_review_target"] == LIKELY_POST_PACKET_REVIEW_TARGET
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["phi_transport_registry_boundary"] == PHI_TRANSPORT_REGISTRY_BOUNDARY
    assert review["prior_phi_transport_candidate_id"] == TRANSPORT_CANDIDATE_ID
    assert review["prior_phi_transport_candidate_type"] == TRANSPORT_CANDIDATE_TYPE
    assert review["prior_phi_transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert (
        review["prior_phi_transport_constraint_equation"]
        == TRANSPORT_CONSTRAINT_EQUATION
    )
    assert (
        review["prior_phi_transport_admissibility_constraint_form"]
        == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
    )
    assert (
        review["prior_phi_transport_closeout_rule_classification"]
        == TRANSPORT_CLOSEOUT_RULE_CLASSIFICATION
    )
    assert review["forbidden_reused_routes"] == FORBIDDEN_REUSED_ROUTES
    assert review["main_watch_item"] == MAIN_WATCH_ITEM

    for key in [
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_transport_phi_discharged",
        "C_transport_phi_theorem_linkage_gap_discharged",
        "C_transport_phi_theorem_linkage_obligation_discharged",
        "C_transport_phi_closure_claimed",
        "gap_discharged",
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
        "master_action_route_substituted",
        "phi_sector_closure_claimed",
        "full_scalar_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "em_qft_closure_claimed",
        "general_C_k_closure",
        "action_embedding_claimed",
        "action_variation_executed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_ck_family_selection_after_phi_bridge_closeout_result_review_records_lean_status() -> None:
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


def test_ck_family_selection_after_phi_bridge_closeout_result_review_rotates_to_transport_packet() -> None:
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
    assert LIKELY_POST_PACKET_REVIEW_TARGET in registry["next_strict_target_coverage"]

    selector = _workstream(
        registry,
        "select_next_ck_family_theorem_linkage_obligation_after_phi_bridge_closeout",
    )
    assert selector["status"] == "paused"
    assert selector["authorization_evidence"] == _rel(SELECTION_LEAN_PACKET_PATH)
    assert selector["report"] == _rel(SELECTION_OUT)
    assert selector["selector_outcome"] == SELECTION_OUTCOME
    assert selector["strict_selector_outcome"] == STRICT_SELECTION_RESULT
    assert selector["selected_next_target"] == consumed_target()

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["likely_packet_outcome"] == LIKELY_PACKET_OUTCOME
    assert consumed["strict_likely_packet_outcome"] == STRICT_LIKELY_PACKET_OUTCOME
    assert consumed["selected_obligation"] == SELECTED_OBLIGATION
    assert consumed["selected_theorem_linkage_gap"] == SELECTED_THEOREM_LINKAGE_GAP
    assert consumed["prior_phi_transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
    assert consumed["prior_phi_transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
    assert consumed["C_transport_phi_discharged"] == "no"
    assert consumed["proof_attempt_executed"] == "no"
    assert consumed["theorem_discharged"] == "no"
    assert consumed["C_source_phi_route_reused"] == "no"
    assert consumed["C_bridge_phi_route_reused"] == "no"
    assert consumed["A_sector_route_imported"] == "no"
    assert consumed["psi_A_route_imported"] == "no"
    assert consumed["QFT_GR_route_imported"] == "no"
    assert consumed["master_action_route_substituted"] == "no"
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
        assert active["consumed_target"] == consumed_target()
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["packet_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["selected_obligation"] == SELECTED_OBLIGATION
        assert active["next_packet_scope"] == NEXT_PACKET_SCOPE_INSTRUCTION
        assert active["likely_packet_outcome"] == LIKELY_PACKET_OUTCOME
        assert active["strict_likely_packet_outcome"] == STRICT_LIKELY_PACKET_OUTCOME
        assert active["prior_phi_transport_constraint_form"] == TRANSPORT_CONSTRAINT_FORM
        assert active["prior_phi_transport_constraint_equation"] == TRANSPORT_CONSTRAINT_EQUATION
        assert active["main_watch_item"] == MAIN_WATCH_ITEM
        assert active["proof_execution_authorized"] == "no"
        assert active["C_transport_phi_discharged"] == "no"
        assert active["theorem_discharged"] == "no"
        assert active["C_source_phi_route_reused"] == "no"
        assert active["C_bridge_phi_route_reused"] == "no"
        assert active["A_sector_route_imported"] == "no"
        assert active["psi_A_route_imported"] == "no"
        assert active["QFT_GR_route_imported"] == "no"
        assert active["master_action_route_substituted"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]


def test_ck_family_selection_after_phi_bridge_closeout_result_review_mirrors() -> None:
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
        "CKFamilyTheoremLinkageObligationSelectionAfterPhiBridgeCloseoutResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_PACKET_OUTCOME,
        STRICT_LIKELY_PACKET_OUTCOME,
        SELECTED_OBLIGATION,
        SELECTED_THEOREM_LINKAGE_GAP,
        PHI_TRANSPORT_REGISTRY_BOUNDARY,
        TRANSPORT_CONSTRAINT_FORM,
        TRANSPORT_CONSTRAINT_EQUATION,
        TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        NEXT_PACKET_SCOPE_INSTRUCTION,
        MAIN_WATCH_ITEM,
        NEXT_PACKET_RECOVERY_ITEMS[0],
        NEXT_PACKET_RECOVERY_ITEMS[-1],
        LEAN_STATUS_WORDING_LINES_FOR_REVIEW[0],
        LEAN_STATUS_WORDING_LINES_FOR_REVIEW[1],
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PHI_BRIDGE_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "no phi transport proof execution",
        "no theorem discharge",
        "no phi-sector closure",
        "no scalar/QFT closure",
        "no QFT-GR closure",
        "no EM-QFT closure",
        "no seam closure",
        "no general C_k closure",
        "no C_k promotion",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_ck_family_selection_after_phi_bridge_closeout_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_obligation_selection_after_phi_bridge_closeout_result_review_gate.py"
    )
