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
    CLOSEOUT_RESULT,
    DEFAULT_OUT as CLOSEOUT_OUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
)
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ADJOINT_DIRAC_EQUATION_SHAPE,
    CURRENT_DEFINITION,
    DEFAULT_OUT,
    DIRAC_EQUATION_SHAPE,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LIKELY_NEXT_OBLIGATION,
    LIKELY_SELECTOR_OUTCOME,
    NEXT_OBLIGATION_REASON,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REVIEW_RESULT,
    ROUTE_STATEMENT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    T_PSI_POLICY,
    WATCH_ITEMS,
    build_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result_review_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
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
POST_SELECTOR_STRICT_OUTCOME = (
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_SELECTS_GAUGE_EXCHANGE_LINKAGE_OBLIGATION_NO_GAP_"
    "DISCHARGE_OR_CK_RULE_PROMOTION"
)
POST_SELECTOR_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseout.lean"
)
POST_SELECTOR_REPORT = (
    "formal/docs/release/"
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_20260628_v0.json"
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
POST_SELECTOR_REVIEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "CKFamilyTheoremLinkageObligationSelectionAfterPsiAMatterExchangeCloseoutResultReview.lean"
)
POST_SELECTOR_REVIEW_REPORT = (
    "formal/docs/release/"
    "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_MATTER_"
    "EXCHANGE_CLOSEOUT_RESULT_REVIEW_20260628_v0.json"
)
POST_SELECTOR_PACKET_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PsiAGaugeSectorExchangeTheoremLinkageObligationPacket.lean"
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
    return "review_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result"


def test_psi_A_matter_exchange_closeout_result_review_files_exist() -> None:
    for path in [
        CLOSEOUT_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_matter_exchange_closeout_result_review_accepts_closeout() -> None:
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
    assert review["likely_selector_outcome"] == LIKELY_SELECTOR_OUTCOME
    assert review["likely_next_obligation"] == LIKELY_NEXT_OBLIGATION
    assert review["next_obligation_reason"] == NEXT_OBLIGATION_REASON
    assert (
        build_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result_review()
        == review
    )


def test_psi_A_matter_exchange_closeout_result_review_preserves_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["closeout_outcome"] == CLOSEOUT_RESULT
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["target_rule"] == TARGET
    assert review["T_psi_policy"] == T_PSI_POLICY
    assert review["dirac_equation_shape"] == DIRAC_EQUATION_SHAPE
    assert review["adjoint_dirac_equation_shape"] == ADJOINT_DIRAC_EQUATION_SHAPE
    assert review["current_definition"] == CURRENT_DEFINITION
    assert review["route_statement"] == ROUTE_STATEMENT
    assert review["watch_items"] == WATCH_ITEMS
    assert review["matter_sector_exchange_closeout_accepted"] is True
    assert review["matter_exchange_linked_to_dirac_pair_route"] is True
    assert review["matter_exchange_route_constructed"] is True
    assert review["matter_exchange_derived"] is True
    assert review["T_psi_policy_preserved"] is True
    assert review["J_definition_preserved"] is True
    assert review["watch_items_preserved"] is True
    assert review["local_psi_A_matter_sector_exchange_obligation_closed"] is True
    assert review["selector_authorized"] is True
    assert review["selector_executed"] is False
    assert review["next_theorem_linkage_obligation_selected"] is False
    assert review["review_executes_new_proof"] is False
    assert review["proof_execution_authorized"] is False

    for key in [
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "general_C_k_closure",
        "general_C_k_theorem_linkage_closure",
        "C_k_dynamical_law_status",
        "gap_1_through_gap_8_discharged",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_psi_A_matter_exchange_closeout_result_review_records_lean_status() -> None:
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


def test_psi_A_matter_exchange_closeout_result_review_rotates_to_selector() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert_historical_target_recorded(
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
    assert NEXT_TARGET in registry["paused_lanes"]
    assert POST_SELECTOR_REVIEW_TARGET in registry["next_strict_target_coverage"]

    closeout = _workstream(
        registry,
        "prepare_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout",
    )
    assert closeout["status"] == "paused"
    assert closeout["authorization_evidence"] == _rel(CLOSEOUT_LEAN_PACKET_PATH)
    assert closeout["report"] == _rel(CLOSEOUT_OUT)
    assert closeout["closeout_result"] == CLOSEOUT_OUTCOME

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["matter_sector_exchange_closeout_accepted"] == "yes"
    assert consumed["matter_exchange_linked_to_dirac_pair_route"] == "yes"
    assert consumed["general_C_k_theorem_linkage_closure"] == "no"
    assert consumed["C_k_dynamical_law_status"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    selector = _workstream(registry, NEXT_TARGET)
    assert selector["status"] == "paused"
    assert selector["authorization_evidence"] == POST_SELECTOR_EVIDENCE
    assert selector["report"] == POST_SELECTOR_REPORT
    assert selector["selection_result"] == POST_SELECTOR_OUTCOME
    assert selector["strict_selection_result"] == POST_SELECTOR_STRICT_OUTCOME
    assert selector["selected_next_target"] == POST_SELECTOR_REVIEW_TARGET
    assert selector["selected_obligation"] == POST_SELECTOR_SELECTED_OBLIGATION
    assert selector["proof_attempt_executed"] == "no"
    assert selector["theorem_discharged"] == "no"
    assert selector["rule_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == GAUGE_ATTEMPT_REVIEW_TARGET
    assert active["active_lane"] == active["workstream_id"]
    assert active["authorization_evidence"] == GAUGE_ATTEMPT_EVIDENCE
    assert active["authorized_next_strict_target"] == active["workstream_id"]
    assert active["consumed_target"] == GAUGE_ATTEMPT_PREPARATION_TARGET
    assert active["report"] == GAUGE_ATTEMPT_REPORT
    assert active["packet_result"] == GAUGE_ATTEMPT_OUTCOME
    assert active["attempt_preparation_result"] == GAUGE_ATTEMPT_OUTCOME
    assert active["strict_attempt_preparation_result"] == GAUGE_ATTEMPT_STRICT_OUTCOME
    assert active["review_result"] == "PENDING"
    assert active["execution_result"] == "PENDING"
    assert active["selected_next_target"] == GAUGE_ATTEMPT_EXECUTION_TARGET
    assert active["selected_obligation"] == POST_SELECTOR_SELECTED_OBLIGATION
    assert active["proof_execution_authorized"] == "no"
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_matter_exchange_closeout_result_review_mirrors() -> None:
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
        "PsiAMatterSectorExchangeTheoremLinkageObligationCloseoutResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_SELECTOR_OUTCOME,
        LIKELY_NEXT_OBLIGATION,
        NEXT_OBLIGATION_REASON,
        THEOREM_TARGET_STATEMENT,
        TARGET,
        T_PSI_POLICY,
        CURRENT_DEFINITION,
        ROUTE_STATEMENT,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "matter-sector exchange theorem-linkage closeout accepted",
        "psi-A gauge-sector exchange theorem-linkage gap",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no general C_k closure",
        "no C_k dynamical-law status",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_matter_exchange_closeout_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result_review_gate.py"
    )
