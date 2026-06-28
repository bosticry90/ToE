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
    skip_if_not_current_target,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_report import (
    DEFAULT_OUT as SELECTION_OUT,
    LEAN_PACKET_PATH as SELECTION_LEAN_PACKET_PATH,
    NEXT_TARGET as SELECTOR_REVIEW_TARGET,
    OUTCOME_ID as SELECTION_OUTCOME,
    STRICT_SELECTION_RESULT,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result_review_report import (
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GAUGE_EXCHANGE_TARGET_RULE,
    GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LIKELY_POST_PACKET_REVIEW_TARGET,
    NEXT_PACKET_TARGET_STATEMENT,
    NEXT_PACKET_WATCH_ITEMS,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REVIEW_ACCEPTANCE_SUMMARY,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_RANK,
    SOURCED_MAXWELL_ROUTE,
    STRICT_REVIEW_RESULT,
    build_ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result_review,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_report import (
    DEFAULT_OUT as GAUGE_PACKET_OUT,
    LEAN_PACKET_PATH as GAUGE_PACKET_LEAN_PACKET_PATH,
    LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW as GAUGE_PACKET_FOLLOW_ON_TARGET,
    NEXT_TARGET as GAUGE_PACKET_REVIEW_TARGET,
    OUTCOME_ID as GAUGE_PACKET_OUTCOME,
    STRICT_PACKET_RESULT as GAUGE_PACKET_STRICT_OUTCOME,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_report import (
    DEFAULT_OUT as GAUGE_ATTEMPT_OUT,
    LEAN_PACKET_PATH as GAUGE_ATTEMPT_LEAN_PACKET_PATH,
    LIKELY_POST_REVIEW_TARGET as GAUGE_ATTEMPT_EXECUTION_TARGET,
    NEXT_TARGET as GAUGE_ATTEMPT_REVIEW_TARGET,
    OUTCOME_ID as GAUGE_ATTEMPT_OUTCOME,
    STRICT_ATTEMPT_PREPARATION_RESULT as GAUGE_ATTEMPT_STRICT_OUTCOME,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review_report import (
    DEFAULT_OUT as GAUGE_ATTEMPT_RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as GAUGE_ATTEMPT_RESULT_REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as GAUGE_ATTEMPT_RESULT_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as GAUGE_ATTEMPT_RESULT_REVIEW_STRICT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result_review_report.py"
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
GAUGE_ATTEMPT_PREPARATION_TARGET = (
    "prepare_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
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


def test_post_psi_A_matter_exchange_selection_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_post_psi_A_matter_exchange_selection_result_review_accepts_gauge_exchange_selection() -> None:
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
    assert review["selected_obligation"] == SELECTED_OBLIGATION
    assert review["selected_obligation_rank"] == SELECTED_OBLIGATION_RANK
    assert review["review_acceptance_summary"] == REVIEW_ACCEPTANCE_SUMMARY
    assert (
        build_ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result_review()
        == review
    )


def test_post_psi_A_matter_exchange_selection_result_review_preserves_packet_scope_and_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["gauge_exchange_target_rule"] == GAUGE_EXCHANGE_TARGET_RULE
    assert (
        review["gauge_stress_energy_divergence_identity"]
        == GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
    )
    assert review["sourced_maxwell_route"] == SOURCED_MAXWELL_ROUTE
    assert review["next_packet_target_statement"] == NEXT_PACKET_TARGET_STATEMENT
    assert review["next_packet_watch_items"] == NEXT_PACKET_WATCH_ITEMS
    assert review["follow_on_target_after_review"] == NEXT_TARGET
    assert review["likely_post_packet_review_target"] == LIKELY_POST_PACKET_REVIEW_TARGET
    assert review["proof_execution_authorized"] is False
    assert review["proof_attempt_executed"] is False
    assert review["theorem_discharged"] is False
    assert review["theorem_linkage_obligation_discharged"] is False
    assert review["proof_debt_discharged"] is False
    assert review["gap_1_through_gap_8_discharged"] is False
    assert review["rule_promoted"] is False
    assert review["C_k_action_embedding_claimed"] is False
    assert review["C_k_action_variation_executed"] is False
    assert review["full_maxwell_closure_claimed"] is False
    assert review["em_qft_closure_claimed"] is False
    assert review["qft_gr_closure_claimed"] is False
    assert review["gr_qm_closure_claimed"] is False
    assert review["seam_closure_claim"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False


def test_post_psi_A_matter_exchange_selection_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_REVIEW
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


def test_post_psi_A_matter_exchange_selection_result_review_rotates_to_gauge_exchange_packet() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    skip_if_not_current_target(registry, GAUGE_ATTEMPT_EXECUTION_TARGET)

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

    assert is_current is False
    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert GAUGE_PACKET_REVIEW_TARGET in registry["next_strict_target_coverage"]

    selector = _workstream(
        registry,
        "select_next_ck_family_theorem_linkage_obligation_after_psi_A_matter_exchange_closeout",
    )
    assert selector["status"] == "paused"
    assert selector["authorization_evidence"] == _rel(SELECTION_LEAN_PACKET_PATH)
    assert selector["report"] == _rel(SELECTION_OUT)
    assert selector["selection_result"] == SELECTION_OUTCOME
    assert selector["strict_selection_result"] == STRICT_SELECTION_RESULT
    assert selector["selected_next_target"] == consumed_target()

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["selected_obligation"] == SELECTED_OBLIGATION
    assert consumed["selected_obligation_rank"] == str(SELECTED_OBLIGATION_RANK)
    assert consumed["proof_attempt_executed"] == "no"
    assert consumed["theorem_discharged"] == "no"
    assert consumed["rule_promoted"] == "no"

    packet = _workstream(registry, NEXT_TARGET)
    assert packet["status"] == "paused"
    assert packet["authorization_evidence"] == _rel(GAUGE_PACKET_LEAN_PACKET_PATH)
    assert packet["report"] == _rel(GAUGE_PACKET_OUT)
    assert packet["packet_result"] == GAUGE_PACKET_OUTCOME
    assert packet["strict_packet_result"] == GAUGE_PACKET_STRICT_OUTCOME
    assert packet["selected_next_target"] == GAUGE_PACKET_REVIEW_TARGET
    assert packet["selected_obligation"] == SELECTED_OBLIGATION
    assert packet["proof_attempt_executed"] == "no"
    assert packet["theorem_discharged"] == "no"
    assert packet["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == GAUGE_ATTEMPT_EXECUTION_TARGET
    assert active["active_lane"] == GAUGE_ATTEMPT_EXECUTION_TARGET
    assert active["authorization_evidence"] == _rel(
        GAUGE_ATTEMPT_RESULT_REVIEW_LEAN_PACKET_PATH
    )
    assert active["report"] == _rel(GAUGE_ATTEMPT_RESULT_REVIEW_OUT)
    assert active["packet_result"] == GAUGE_ATTEMPT_RESULT_REVIEW_OUTCOME
    assert active["attempt_preparation_result"] == GAUGE_ATTEMPT_OUTCOME
    assert active["strict_attempt_preparation_result"] == GAUGE_ATTEMPT_STRICT_OUTCOME
    assert active["review_result"] == GAUGE_ATTEMPT_RESULT_REVIEW_OUTCOME
    assert active["strict_review_result"] == GAUGE_ATTEMPT_RESULT_REVIEW_STRICT_OUTCOME
    assert active["execution_result"] == "PENDING"
    assert active["consumed_target"] == GAUGE_ATTEMPT_REVIEW_TARGET
    assert active["selected_next_target"] == GAUGE_ATTEMPT_REVIEW_TARGET
    assert active["selected_obligation"] == SELECTED_OBLIGATION
    assert active["proof_execution_authorized"] == "yes"
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_post_psi_A_matter_exchange_selection_result_review_mirrors() -> None:
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
        "CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseoutResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SELECTED_OBLIGATION,
        GAUGE_EXCHANGE_TARGET_RULE,
        GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
        SOURCED_MAXWELL_ROUTE,
        NEXT_PACKET_TARGET_STATEMENT,
        NEXT_PACKET_WATCH_ITEMS[0],
        NEXT_PACKET_WATCH_ITEMS[-1],
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_EXCHANGE_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "no proof execution",
        "no theorem discharge",
        "no GAP-1 through GAP-8",
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


def test_post_psi_A_matter_exchange_selection_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result_review_gate.py"
    )
