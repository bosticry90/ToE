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
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_report import (
    AVOIDED_CLAIMS,
    DEFAULT_OUT,
    DEPENDENCY_CHAIN,
    FOLLOW_ON_TARGET_AFTER_REVIEW,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_SELECTION,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_SELECTION,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    ROUTE_BOUNDARY,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_SELECTION,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_ROW_ID,
    SELECTED_THEOREM_LINKAGE_GAP,
    STRICT_SELECTION_RESULT,
    build_ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as RESULT_REVIEW_NEXT_TARGET,
    NEXT_TARGET_KIND as RESULT_REVIEW_NEXT_TARGET_KIND,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as RESULT_REVIEW_STRICT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_report.py"
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
CONSUMED_TARGET = (
    "select_next_ck_family_theorem_linkage_obligation_after_"
    "psi_A_exchange_chain_closeout"
)
CONSUMED_REVIEW_TARGET = (
    "review_psi_A_interaction_exchange_theorem_linkage_chain_closeout_result"
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


def test_ck_family_selection_after_psi_A_exchange_chain_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_ck_family_selection_after_psi_A_exchange_chain_selects_C_source_A() -> None:
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
        build_ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout()
        == selection
    )


def test_ck_family_selection_after_psi_A_exchange_chain_preserves_selector_boundary() -> None:
    selection = _json(DEFAULT_OUT)

    assert selection["dependency_chain"] == DEPENDENCY_CHAIN
    assert selection["plain_meaning"] == PLAIN_MEANING
    assert selection["route_boundary"] == ROUTE_BOUNDARY
    assert selection["avoided_claims"] == AVOIDED_CLAIMS
    assert selection["selector_only"] is True
    assert selection["proof_execution_authorized"] is False
    assert selection["proof_attempt_executed"] is False
    assert selection["theorem_discharged"] is False
    assert selection["theorem_linkage_obligation_discharged"] is False
    assert selection["gap_discharged"] is False
    assert selection["rule_promoted"] is False
    assert selection["A_sector_closure_claimed"] is False
    assert selection["sourced_maxwell_closure_claimed"] is False
    assert selection["full_maxwell_closure_claimed"] is False
    assert selection["em_qft_closure_claimed"] is False
    assert selection["qft_gr_closure_claimed"] is False
    assert selection["gr_qm_closure_claimed"] is False
    assert selection["seam_closure_claim"] is False
    assert selection["empirical_validation_claimed"] is False
    assert selection["master_action_promoted"] is False


def test_ck_family_selection_after_psi_A_exchange_chain_records_lean_status() -> None:
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


def test_ck_family_selection_after_psi_A_exchange_chain_rotates_to_review() -> None:
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

    assert CONSUMED_REVIEW_TARGET in registry["completed_targets"]
    assert CONSUMED_REVIEW_TARGET in registry["consumed_targets"]
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
    assert selector["proof_execution_authorized"] == "no"
    assert selector["gap_discharged"] == "no"
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
        assert active["proof_execution_authorized"] == "no"
        assert active["gap_discharged"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        review_evidence = _rel(RESULT_REVIEW_LEAN_PACKET_PATH)
        review_report = _rel(RESULT_REVIEW_OUT)
        review_row = _workstream(registry, NEXT_TARGET)
        assert review_row["status"] == "paused"
        assert review_row["authorization_evidence"] == review_evidence
        assert review_row["report"] == review_report
        assert review_row["review_result"] == RESULT_REVIEW_OUTCOME
        assert review_row["strict_review_result"] == RESULT_REVIEW_STRICT_OUTCOME
        assert review_row["selected_next_target"] == RESULT_REVIEW_NEXT_TARGET
        assert review_row["selected_next_target_kind"] == RESULT_REVIEW_NEXT_TARGET_KIND
        assert review_row["selected_obligation"] == SELECTED_OBLIGATION
        assert review_row["proof_execution_authorized"] == "no"
        assert review_row["gap_discharged"] == "no"
        assert review_row["rule_promoted"] == "no"
        assert review_row["master_action_promoted"] == "no"

        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == RESULT_REVIEW_NEXT_TARGET
        assert active["active_lane"] == RESULT_REVIEW_NEXT_TARGET
        assert active["authorization_evidence"] == review_evidence
        assert active["report"] == review_report
        assert active["authorized_next_strict_target"] == RESULT_REVIEW_NEXT_TARGET
        assert active["consumed_target"] == NEXT_TARGET
        assert active["review_result"] == RESULT_REVIEW_OUTCOME
        assert active["strict_review_result"] == RESULT_REVIEW_STRICT_OUTCOME
        assert active["packet_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["selected_obligation"] == SELECTED_OBLIGATION
        assert active["proof_execution_authorized"] == "no"
        assert active["gap_discharged"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"


def test_ck_family_selection_after_psi_A_exchange_chain_mirrors() -> None:
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
        "CKFamilyTheoremLinkageObligationSelectionAfterPsiAExchangeChainCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        FOLLOW_ON_TARGET_AFTER_REVIEW,
        SELECTED_OBLIGATION,
        SELECTED_THEOREM_LINKAGE_GAP,
        ROUTE_BOUNDARY,
        LEAN_STATUS_WORDING_FOR_SELECTION,
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_CLOSEOUT_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_EXCHANGE_CHAIN_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "do not execute the C_source^A proof route",
        "do not claim A-sector closure",
        "do not claim full Maxwell closure",
        "do not claim sourced Maxwell closure",
        "do not claim EM-QFT closure",
        "do not claim QFT-GR closure",
        "do not upgrade C_source^A to a dynamical law",
        "do not promote the master action",
    ]:
        assert token in joined, token


def test_ck_family_selection_after_psi_A_exchange_chain_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_obligation_selection_after_psi_A_exchange_chain_closeout_gate.py"
    )
