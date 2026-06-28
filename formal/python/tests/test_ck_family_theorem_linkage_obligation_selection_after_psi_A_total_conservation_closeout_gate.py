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
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_total_conservation_closeout_report import (
    DEFAULT_OUT,
    DEPENDENCY_CHAIN,
    FOLLOW_ON_TARGET_AFTER_REVIEW,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_SELECTION,
    MATTER_EXCHANGE_TARGET_RULE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PREVIOUS_CLOSED_OBLIGATION,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_RANK,
    STRICT_SELECTION_RESULT,
    THEOREM_TARGET_STATUS,
    WATCH_ITEMS,
    build_ck_family_theorem_linkage_obligation_selection_after_psi_A_total_conservation_closeout,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_total_conservation_closeout_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    LIKELY_POST_PACKET_REVIEW_TARGET,
    NEXT_TARGET as RESULT_REVIEW_NEXT_TARGET,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as RESULT_REVIEW_STRICT_REVIEW_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_obligation_selection_after_psi_A_total_conservation_closeout_report.py"
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


def selection_consumed_target() -> str:
    return (
        "select_next_ck_family_theorem_linkage_obligation_after_"
        "psi_A_total_conservation_closeout"
    )


def test_ck_family_selection_after_psi_A_total_conservation_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_selection_after_psi_A_total_conservation_selects_matter_exchange() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["artifact_id"] == SCHEMA_ID
    assert selection["schema_id"] == SCHEMA_ID
    assert selection["packet_id"] == PACKET_ID
    assert selection["prepared"] is True
    assert selection["accepted"] is True
    assert selection["selected"] is True
    assert selection["outcome_id"] == OUTCOME_ID
    assert selection["selection_result"] == OUTCOME_ID
    assert selection["packet_result"] == OUTCOME_ID
    assert selection["strict_selection_result"] == STRICT_SELECTION_RESULT
    assert selection["packet_classification"] == PACKET_CLASSIFICATION
    assert selection["previous_closed_obligation"] == PREVIOUS_CLOSED_OBLIGATION
    assert selection["previous_closed_obligation_local_only"] is True
    assert selection["selected_obligation"] == SELECTED_OBLIGATION
    assert selection["selected_obligation_rank"] == SELECTED_OBLIGATION_RANK
    assert selection["selected_obligation_from_priority_list"] is True
    assert selection["selected_next_target"] == NEXT_TARGET
    assert selection["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert selection["follow_on_target_after_review"] == FOLLOW_ON_TARGET_AFTER_REVIEW
    assert (
        build_ck_family_theorem_linkage_obligation_selection_after_psi_A_total_conservation_closeout()
        == selection
    )


def test_ck_family_selection_after_psi_A_total_conservation_records_watch_items_only() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["dependency_chain"] == DEPENDENCY_CHAIN
    assert selection["matter_exchange_target_rule"] == MATTER_EXCHANGE_TARGET_RULE
    assert selection["theorem_target_status"] == THEOREM_TARGET_STATUS
    assert selection["watch_items"] == WATCH_ITEMS
    assert selection["proof_execution_authorized"] is False
    assert selection["proof_attempt_executed"] is False
    assert selection["theorem_discharged"] is False
    assert selection["theorem_linkage_obligation_discharged"] is False
    assert selection["proof_debt_discharged"] is False
    assert selection["gap_1_through_gap_8_discharged"] is False
    assert selection["rule_promoted"] is False
    assert selection["C_k_action_embedding_claimed"] is False
    assert selection["C_k_action_variation_executed"] is False
    assert selection["full_maxwell_closure_claimed"] is False
    assert selection["em_qft_closure_claimed"] is False
    assert selection["qft_gr_closure_claimed"] is False
    assert selection["gr_qm_closure_claimed"] is False
    assert selection["seam_closure_claim"] is False
    assert selection["empirical_validation_claimed"] is False
    assert selection["master_action_promoted"] is False


def test_ck_family_selection_after_psi_A_total_conservation_records_lean_status() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_SELECTION
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


def test_ck_family_selection_after_psi_A_total_conservation_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    review_evidence = _rel(RESULT_REVIEW_LEAN_PACKET_PATH)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()
    assert_historical_target_recorded(
        payload=registry,
        previous_target=selection_consumed_target(),
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )

    assert selection_consumed_target() in registry["completed_targets"]
    assert selection_consumed_target() in registry["consumed_targets"]
    assert selection_consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert RESULT_REVIEW_NEXT_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert RESULT_REVIEW_NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, selection_consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["selection_result"] == OUTCOME_ID
    assert consumed["strict_selection_result"] == STRICT_SELECTION_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["selected_obligation"] == SELECTED_OBLIGATION
    assert consumed["proof_attempt_executed"] == "no"
    assert consumed["theorem_discharged"] == "no"
    assert consumed["rule_promoted"] == "no"

    review = _workstream(registry, NEXT_TARGET)
    assert review["status"] == "paused"
    assert review["authorization_evidence"] == review_evidence
    assert review["report"] == _rel(RESULT_REVIEW_OUT)
    assert review["selection_result"] == OUTCOME_ID
    assert review["review_result"] == RESULT_REVIEW_OUTCOME
    assert review["strict_review_result"] == RESULT_REVIEW_STRICT_REVIEW_RESULT
    assert review["selected_next_target"] == RESULT_REVIEW_NEXT_TARGET
    assert review["selected_obligation"] == SELECTED_OBLIGATION
    assert review["proof_attempt_executed"] == "no"
    assert review["theorem_discharged"] == "no"
    assert review["rule_promoted"] == "no"
    assert review["master_action_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == RESULT_REVIEW_NEXT_TARGET
    assert active["authorization_evidence"] == review_evidence
    assert active["report"] == _rel(RESULT_REVIEW_OUT)
    assert active["consumed_target"] == NEXT_TARGET
    assert active["review_result"] == RESULT_REVIEW_OUTCOME
    assert active["packet_result"] == "PENDING"
    assert active["selected_next_target"] == LIKELY_POST_PACKET_REVIEW_TARGET
    assert active["selected_obligation"] == SELECTED_OBLIGATION
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_ck_family_selection_after_psi_A_total_conservation_mirrors() -> None:
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
        "CKFamilyTheoremLinkageObligationSelectionAfterPsiATotalConservationCloseout",
        selection_consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        FOLLOW_ON_TARGET_AFTER_REVIEW,
        SELECTED_OBLIGATION,
        MATTER_EXCHANGE_TARGET_RULE,
        WATCH_ITEMS[0],
        WATCH_ITEMS[-1],
        LEAN_STATUS_WORDING_FOR_SELECTION,
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_TOTAL_CONSERVATION_CLOSEOUT_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_TOTAL_CONSERVATION_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "no proof execution",
        "no theorem discharge",
        "no GAP-1 through GAP-8 global discharge",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_ck_family_selection_after_psi_A_total_conservation_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_obligation_selection_after_psi_A_total_conservation_closeout_gate.py"
    )
