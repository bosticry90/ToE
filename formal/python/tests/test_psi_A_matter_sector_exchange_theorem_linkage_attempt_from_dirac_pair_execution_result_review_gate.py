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
    workstream,
)
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    CLOSEOUT_OUTCOME,
    CLOSEOUT_STATEMENT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EXECUTION_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    REVIEW_RESULT,
    ROUTE_STATEMENT,
    ROUTE_STEPS,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_result_review,
)
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_report import (
    EXECUTION_RESULT,
    STRICT_EXECUTION_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_result_review_report.py"
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
CLOSEOUT_REVIEW_TARGET = (
    "review_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout_result"
)
POST_CLOSEOUT_SELECTOR_TARGET = (
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
GAUGE_ATTEMPT_PREPARATION_TARGET = (
    "prepare_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
)
GAUGE_ATTEMPT_REVIEW_TARGET = (
    "review_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result"
)
GAUGE_ATTEMPT_EXECUTION_TARGET = (
    "execute_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
)
GAUGE_ATTEMPT_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "PREPARED_GAUGE_EXCHANGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
GAUGE_ATTEMPT_RESULT_REVIEW_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "RESULT_REVIEW_ACCEPTS_GAUGE_EXCHANGE_ROUTE_PREPARATION_NO_THEOREM_DISCHARGE_"
    "OR_CK_RULE_PROMOTION"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_psi_A_matter_exchange_attempt_execution_result_review_files_exist() -> None:
    for path in [
        EXECUTION_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_matter_exchange_attempt_execution_result_review_accepts_route() -> None:
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
    assert review["closeout_outcome"] == CLOSEOUT_OUTCOME
    assert review["closeout_statement"] == CLOSEOUT_STATEMENT
    assert (
        build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_result_review()
        == review
    )


def test_psi_A_matter_exchange_attempt_execution_result_review_records_scope() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["claim_boundary"] == "theorem-linkage result review only, not physics closure"
    assert review["target_rule"] == TARGET
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["route_steps"] == ROUTE_STEPS
    assert review["route_statement"] == ROUTE_STATEMENT
    assert review["plain_meaning"] == PLAIN_MEANING
    assert review["matter_exchange_route_constructed"] is True
    assert review["matter_exchange_derived"] is True
    assert review["local_theorem_linkage_reduced"] is True
    assert review["closeout_preparation_authorized"] is True
    assert review["review_executes_attempt"] is False
    assert review["proof_execution_authorized"] is False
    assert review["proof_attempt_executed"] is True
    assert review["theorem_discharged"] is True
    assert review["theorem_linkage_completed"] is True
    assert review["theorem_linkage_proof_attempt_authorized"] is False

    for key in [
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "multiplier_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_psi_A_matter_exchange_attempt_execution_result_review_records_lean_status() -> None:
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


def test_psi_A_matter_exchange_attempt_execution_result_review_rotates_to_closeout() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    if is_current:
        assert NEXT_TARGET not in registry["paused_lanes"]
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    reviewed = workstream(CONSUMED_TARGET, registry)
    assert reviewed["status"] == "paused"
    assert reviewed["authorization_evidence"] == evidence
    assert reviewed["report"] == _rel(DEFAULT_OUT)
    assert reviewed["review_result"] == OUTCOME_ID
    assert reviewed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert reviewed["execution_result"] == EXECUTION_RESULT
    assert reviewed["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert reviewed["selected_next_target"] == NEXT_TARGET
    assert reviewed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert reviewed["review_executes_attempt"] == "no"
    assert reviewed["proof_attempt_executed"] == "yes"
    assert reviewed["theorem_discharged"] == "yes"
    assert reviewed["rule_promoted"] == "no"
    assert reviewed["master_action_promoted"] == "no"

    if is_current:
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["report"] == _rel(DEFAULT_OUT)
        assert active["consumed_target"] == CONSUMED_TARGET
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["execution_result"] == EXECUTION_RESULT
        assert active["suggested_closeout_outcome"] == CLOSEOUT_OUTCOME
        assert active["closeout_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        closeout = workstream(NEXT_TARGET, registry)
        assert closeout["status"] == "paused"
        assert closeout["closeout_result"] == CLOSEOUT_OUTCOME
        assert closeout["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
        assert closeout["rule_promoted"] == "no"
        assert closeout["master_action_promoted"] == "no"

        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] in {
            CLOSEOUT_REVIEW_TARGET,
            POST_CLOSEOUT_SELECTOR_TARGET,
            POST_SELECTOR_REVIEW_TARGET,
            POST_SELECTOR_PACKET_TARGET,
            POST_SELECTOR_PACKET_REVIEW_TARGET,
            GAUGE_ATTEMPT_PREPARATION_TARGET,
            GAUGE_ATTEMPT_REVIEW_TARGET,
            GAUGE_ATTEMPT_EXECUTION_TARGET,
        }
        assert active["consumed_target"] in {
            NEXT_TARGET,
            CLOSEOUT_REVIEW_TARGET,
            POST_CLOSEOUT_SELECTOR_TARGET,
            POST_SELECTOR_REVIEW_TARGET,
            POST_SELECTOR_PACKET_TARGET,
            POST_SELECTOR_PACKET_REVIEW_TARGET,
            GAUGE_ATTEMPT_PREPARATION_TARGET,
            GAUGE_ATTEMPT_REVIEW_TARGET,
            GAUGE_ATTEMPT_EXECUTION_TARGET,
        }
        if active["workstream_id"] == CLOSEOUT_REVIEW_TARGET:
            assert active["closeout_result"] == CLOSEOUT_OUTCOME
        elif active["workstream_id"] == POST_CLOSEOUT_SELECTOR_TARGET:
            assert active["review_result"] == (
                "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_"
                "REVIEW_ACCEPTS_DIRAC_PAIR_LINKED_MATTER_EXCHANGE_ROUTE_NO_CK_RULE_"
                "PROMOTION_OR_SEAM_CLOSURE"
            )
        elif active["workstream_id"] == POST_SELECTOR_REVIEW_TARGET:
            assert active["selection_result"] == POST_SELECTOR_OUTCOME
            assert active["review_result"] == "PENDING"
        elif active["workstream_id"] == POST_SELECTOR_PACKET_TARGET:
            assert active["consumed_target"] == POST_SELECTOR_REVIEW_TARGET
        elif active["workstream_id"] == POST_SELECTOR_PACKET_REVIEW_TARGET:
            assert active["consumed_target"] == POST_SELECTOR_PACKET_TARGET
            assert active["review_result"] == "PENDING"
        elif active["workstream_id"] == GAUGE_ATTEMPT_PREPARATION_TARGET:
            assert active["consumed_target"] == POST_SELECTOR_PACKET_REVIEW_TARGET
            assert active["review_result"] == (
                "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_"
                "ACCEPTS_GAUGE_EXCHANGE_ROUTE_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
            )
        elif active["workstream_id"] == GAUGE_ATTEMPT_REVIEW_TARGET:
            assert active["consumed_target"] in {
                GAUGE_ATTEMPT_PREPARATION_TARGET,
                GAUGE_ATTEMPT_EXECUTION_TARGET,
            }
            if active["consumed_target"] == GAUGE_ATTEMPT_EXECUTION_TARGET:
                assert active["execution_result"] != "PENDING"
                assert active["review_result"] == "PENDING"
                assert active["selected_next_target"] == GAUGE_ATTEMPT_REVIEW_TARGET
            else:
                assert active["attempt_preparation_result"] == GAUGE_ATTEMPT_OUTCOME
                assert active["review_result"] == "PENDING"
                assert active["selected_next_target"] == GAUGE_ATTEMPT_EXECUTION_TARGET
        else:
            assert active["workstream_id"] == GAUGE_ATTEMPT_EXECUTION_TARGET
            assert active["consumed_target"] == GAUGE_ATTEMPT_REVIEW_TARGET
            assert active["attempt_preparation_result"] == GAUGE_ATTEMPT_OUTCOME
            assert active["review_result"] == GAUGE_ATTEMPT_RESULT_REVIEW_OUTCOME
            assert active["execution_result"] == "PENDING"
            assert active["selected_next_target"] == GAUGE_ATTEMPT_REVIEW_TARGET
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"


def test_psi_A_matter_exchange_attempt_execution_result_review_mirrors() -> None:
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
        "PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairExecutionResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        CLOSEOUT_OUTCOME,
        CLOSEOUT_STATEMENT,
        TARGET,
        THEOREM_TARGET_STATEMENT,
        ROUTE_STATEMENT,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "matter-sector exchange theorem-linkage route constructed",
        "Dirac equation and adjoint equation used",
        "T_psi policy used",
        "no C_k promotion",
        "no action embedding",
        "no variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_matter_exchange_attempt_execution_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_result_review_gate.py"
    )
