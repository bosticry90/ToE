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
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_report import (
    ADJOINT_DIRAC_EQUATION_SHAPE,
    CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    CONSUMED_TARGET,
    CURRENT_DEFINITION,
    DEFAULT_OUT,
    DIRAC_EQUATION_SHAPE,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LIKELY_NEXT_OBLIGATION,
    LIKELY_NEXT_OBLIGATION_REASON,
    LIKELY_NEXT_SELECTOR_TARGET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    ROUTE_STATEMENT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    STRICT_CLOSEOUT_RESULT,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    T_PSI_POLICY,
    WATCH_ITEMS,
    build_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_report.py"
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
RESULT_REVIEW_TARGET = (
    "review_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result"
)
SELECTOR_TARGET = (
    "select_next_ck_family_theorem_linkage_obligation_after_psi_A_matter_exchange_closeout"
)
POST_SELECTOR_REVIEW_TARGET = (
    "review_ck_family_theorem_linkage_obligation_selection_after_"
    "psi_A_matter_exchange_closeout_result"
)
POST_SELECTOR_PACKET_TARGET = (
    "prepare_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet"
)
POST_SELECTOR_PACKET_REVIEW_TARGET = (
    "review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result"
)
POST_SELECTOR_OUTCOME = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_SELECTS_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_"
    "GAP_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
)
RESULT_REVIEW_OUTCOME = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_"
    "REVIEW_ACCEPTS_DIRAC_PAIR_LINKED_MATTER_EXCHANGE_ROUTE_NO_CK_RULE_"
    "PROMOTION_OR_SEAM_CLOSURE"
)
RESULT_REVIEW_REPORT = (
    "formal/docs/release/PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_"
    "CLOSEOUT_RESULT_REVIEW_20260628_v0.json"
)
RESULT_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PsiAMatterSectorExchangeTheoremLinkageObligationCloseoutResultReview.lean"
)
POST_SELECTOR_REVIEW_OUTCOME = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_RESULT_REVIEW_ACCEPTS_PSI_A_GAUGE_SECTOR_EXCHANGE_"
    "THEOREM_LINKAGE_GAP_SELECTION_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
)
POST_SELECTOR_REVIEW_STRICT_OUTCOME = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_RESULT_REVIEW_ACCEPTS_GAUGE_EXCHANGE_SELECTION_ONLY_"
    "NO_GAP_DISCHARGE_OR_CK_RULE_PROMOTION"
)
POST_SELECTOR_REVIEW_REPORT = (
    "formal/docs/release/"
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_RESULT_REVIEW_20260628_v0.json"
)
POST_SELECTOR_PACKET_REPORT = (
    "formal/docs/release/"
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260628_v0.json"
)
POST_SELECTOR_SELECTED_OBLIGATION = "psi-A gauge-sector exchange theorem-linkage gap"
GAUGE_ATTEMPT_PREPARATION_TARGET = (
    "prepare_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
)
GAUGE_ATTEMPT_REVIEW_TARGET = (
    "review_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result"
)
GAUGE_ATTEMPT_EXECUTION_TARGET = (
    "execute_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
)
GAUGE_ATTEMPT_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRoute.lean"
)
GAUGE_ATTEMPT_REPORT = (
    "formal/docs/release/"
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "20260628_v0.json"
)
GAUGE_ATTEMPT_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "PREPARED_GAUGE_EXCHANGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
GAUGE_ATTEMPT_STRICT_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "PREPARED_STRESS_DIVERGENCE_TO_CURRENT_EXCHANGE_ROUTE_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
GAUGE_ATTEMPT_RESULT_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteResultReview.lean"
)
GAUGE_ATTEMPT_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "RESULT_REVIEW_20260628_v0.json"
)
GAUGE_ATTEMPT_RESULT_REVIEW_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_GAUGE_EXCHANGE_ROUTE_PREPARATION_NO_THEOREM_DISCHARGE_"
    "OR_CK_RULE_PROMOTION"
)
GAUGE_ATTEMPT_RESULT_REVIEW_STRICT_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_PREPARED_STRESS_DIVERGENCE_TO_CURRENT_EXCHANGE_ROUTE_"
    "NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
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


def test_psi_A_matter_exchange_closeout_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_matter_exchange_closeout_accepts_local_dirac_pair_linkage() -> None:
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
    assert closeout["likely_next_selector_target_after_review"] == (
        LIKELY_NEXT_SELECTOR_TARGET
    )
    assert closeout["likely_next_obligation_after_closeout"] == LIKELY_NEXT_OBLIGATION
    assert closeout["likely_next_obligation_reason"] == LIKELY_NEXT_OBLIGATION_REASON
    assert closeout["closeout_statement"] == CLOSEOUT_STATEMENT
    assert (
        build_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout()
        == closeout
    )


def test_psi_A_matter_exchange_closeout_records_claims_and_nonclaims() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["closeout_claims"] == CLOSEOUT_CLAIMS
    assert closeout["nonclaims"] == NONCLAIMS
    assert closeout["claim_boundary"] == CLAIM_BOUNDARY
    assert closeout["target_rule"] == TARGET
    assert closeout["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert closeout["T_psi_policy"] == T_PSI_POLICY
    assert closeout["dirac_equation_shape"] == DIRAC_EQUATION_SHAPE
    assert closeout["adjoint_dirac_equation_shape"] == ADJOINT_DIRAC_EQUATION_SHAPE
    assert closeout["current_definition"] == CURRENT_DEFINITION
    assert closeout["watch_items"] == WATCH_ITEMS
    assert closeout["route_statement"] == ROUTE_STATEMENT
    assert closeout["matter_exchange_route_constructed"] is True
    assert closeout["matter_exchange_derived"] is True
    assert closeout["matter_exchange_linked_to_dirac_pair_route"] is True
    assert closeout["matter_sector_exchange_obligation_locally_closed"] is True
    assert closeout["local_psi_A_matter_sector_exchange_obligation_closed"] is True
    assert closeout["T_psi_policy_used"] is True
    assert closeout["J_definition_preserved"] is True
    assert closeout["watch_items_preserved"] is True
    assert closeout["closeout_executes_new_proof"] is False
    assert closeout["proof_execution_authorized"] is False

    for key in [
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "general_C_k_closure",
        "general_C_k_theorem_linkage_closure",
        "gap_1_through_gap_8_discharged",
        "C_k_dynamical_law_status",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "multiplier_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert closeout[key] is False, key


def test_psi_A_matter_exchange_closeout_records_lean_status() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_CLOSEOUT
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


def test_psi_A_matter_exchange_closeout_rotates_to_result_review() -> None:
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
    if is_current:
        assert NEXT_TARGET not in registry["paused_lanes"]
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]
        assert SELECTOR_TARGET in registry["next_strict_target_coverage"]
        assert POST_SELECTOR_REVIEW_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["matter_sector_exchange_obligation_locally_closed"] == "yes"
    assert consumed["matter_exchange_linked_to_dirac_pair_route"] == "yes"
    assert consumed["general_C_k_theorem_linkage_closure"] == "no"
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
        assert active["consumed_target"] == CONSUMED_TARGET
        assert active["closeout_result"] == OUTCOME_ID
        assert active["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
        assert active["review_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["matter_sector_exchange_obligation_locally_closed"] == "yes"
        assert active["matter_exchange_linked_to_dirac_pair_route"] == "yes"
        assert active["general_C_k_theorem_linkage_closure"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        review = _workstream(registry, RESULT_REVIEW_TARGET)
        assert review["status"] == "paused"
        assert review["authorization_evidence"] == RESULT_REVIEW_EVIDENCE
        assert review["report"] == RESULT_REVIEW_REPORT
        assert review["review_result"] == RESULT_REVIEW_OUTCOME
        assert review["selected_next_target"] == SELECTOR_TARGET
        assert review["matter_sector_exchange_closeout_accepted"] == "yes"
        assert review["rule_promoted"] == "no"
        assert review["master_action_promoted"] == "no"

        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == GAUGE_ATTEMPT_EXECUTION_TARGET
        assert active["active_lane"] == GAUGE_ATTEMPT_EXECUTION_TARGET
        assert active["authorization_evidence"] == GAUGE_ATTEMPT_RESULT_REVIEW_EVIDENCE
        assert active["authorized_next_strict_target"] == GAUGE_ATTEMPT_EXECUTION_TARGET
        assert active["consumed_target"] == GAUGE_ATTEMPT_REVIEW_TARGET
        assert active["report"] == GAUGE_ATTEMPT_RESULT_REVIEW_REPORT
        assert active["packet_result"] == GAUGE_ATTEMPT_RESULT_REVIEW_OUTCOME
        assert active["attempt_preparation_result"] == GAUGE_ATTEMPT_OUTCOME
        assert active["strict_attempt_preparation_result"] == GAUGE_ATTEMPT_STRICT_OUTCOME
        assert active["review_result"] == GAUGE_ATTEMPT_RESULT_REVIEW_OUTCOME
        assert active["strict_review_result"] == GAUGE_ATTEMPT_RESULT_REVIEW_STRICT_OUTCOME
        assert active["execution_result"] == "PENDING"
        assert active["selected_next_target"] == GAUGE_ATTEMPT_REVIEW_TARGET
        assert active["selected_obligation"] == POST_SELECTOR_SELECTED_OBLIGATION
        assert active["proof_execution_authorized"] == "yes"
        assert active["proof_attempt_executed"] == "no"
        assert active["theorem_discharged"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"


def test_psi_A_matter_exchange_closeout_mirrors() -> None:
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
        "PsiAMatterSectorExchangeTheoremLinkageObligationCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_NEXT_SELECTOR_TARGET,
        LIKELY_NEXT_OBLIGATION,
        CLOSEOUT_STATEMENT,
        TARGET,
        THEOREM_TARGET_STATEMENT,
        ROUTE_STATEMENT,
        LEAN_STATUS_WORDING_FOR_CLOSEOUT,
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_OUTCOME_v0",
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "matter-sector exchange theorem-linkage obligation locally closed",
        "matter exchange linked to Dirac pair route",
        "T_psi policy used",
        "J definition preserved",
        "watch items preserved",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no general C_k closure",
        "no GAP-1 through GAP-8 global discharge",
        "no C_k dynamical-law status",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_matter_exchange_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_gate.py"
    )
