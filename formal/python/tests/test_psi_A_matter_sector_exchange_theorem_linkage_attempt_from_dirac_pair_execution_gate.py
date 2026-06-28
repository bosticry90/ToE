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
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_report import (
    ADJOINT_DIRAC_EQUATION_SHAPE,
    CONSUMED_EXECUTION_TARGET,
    CURRENT_DEFINITION,
    DEFAULT_OUT,
    DIRAC_EQUATION_SHAPE,
    EXECUTION_BLOCKED_CLAIMS,
    EXECUTION_FINDINGS,
    EXECUTION_PROOF_STYLE,
    EXECUTION_RESULT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    RESULT_REVIEW_PATH,
    ROUTE_STATEMENT,
    ROUTE_STEPS,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION,
    STRICT_EXECUTION_RESULT,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    T_PSI_POLICY,
    WATCH_ITEMS,
    build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_report.py"
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
CLOSEOUT_PREPARATION_TARGET = (
    "prepare_psi_A_matter_sector_exchange_theorem_linkage_obligation_closeout"
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


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_psi_A_matter_exchange_attempt_execution_files_exist() -> None:
    for path in [
        RESULT_REVIEW_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_matter_exchange_attempt_execution_report_matches_builder() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["artifact_id"] == SCHEMA_ID
    assert execution["schema_id"] == SCHEMA_ID
    assert execution["packet_id"] == PACKET_ID
    assert execution["prepared"] is True
    assert execution["accepted"] is True
    assert execution["executed"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert execution["packet_result"] == EXECUTION_RESULT
    assert execution["execution_result"] == EXECUTION_RESULT
    assert execution["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert execution["packet_classification"] == PACKET_CLASSIFICATION
    assert execution["consumed_target"] == CONSUMED_EXECUTION_TARGET
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution()
        == execution
    )


def test_psi_A_matter_exchange_attempt_execution_constructs_route() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["execution_findings"] == EXECUTION_FINDINGS
    assert execution["attempt_type"] == "Dirac-pair matter-sector exchange execution"
    assert execution["input_route"] == "Dirac pair plus T_psi policy plus current definition"
    assert execution["target_rule"] == TARGET
    assert execution["proof_style"] == EXECUTION_PROOF_STYLE
    assert execution["claim_boundary"] == "theorem-linkage only, not physics closure"
    assert execution["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert execution["T_psi_policy"] == T_PSI_POLICY
    assert execution["dirac_equation_shape"] == DIRAC_EQUATION_SHAPE
    assert execution["adjoint_dirac_equation_shape"] == ADJOINT_DIRAC_EQUATION_SHAPE
    assert execution["current_definition"] == CURRENT_DEFINITION
    assert execution["route_steps"] == ROUTE_STEPS
    assert execution["route_statement"] == ROUTE_STATEMENT
    assert execution["watch_items"] == WATCH_ITEMS
    assert execution["plain_meaning"] == PLAIN_MEANING
    assert execution["lean_theorem_name"] == LEAN_THEOREM_NAME
    assert execution["matter_exchange_route_constructed"] is True
    assert execution["matter_exchange_derived"] is True
    assert execution["local_theorem_linkage_reduced"] is True
    assert execution["theorem_target_shape"]["therefore"] == TARGET


def test_psi_A_matter_exchange_attempt_execution_preserves_boundaries() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["blocked_claims"] == EXECUTION_BLOCKED_CLAIMS
    assert execution["blocked_claim_count"] == 13
    assert execution["gap_count"] == 8
    assert execution["open_gap_count"] == 8
    assert execution["closed_gap_count"] == 0
    assert execution["proof_execution_authorized"] is True
    assert execution["proof_target_execution_authorized"] is True
    assert execution["proof_attempt_executed"] is True
    assert execution["proof_debt_reduced"] is True
    assert execution["proof_debt_discharged"] is False
    assert execution["theorem_discharged"] is True
    assert execution["theorem_linkage_completed"] is True
    assert execution["theorem_linkage_proof_attempt_authorized"] is True
    assert execution["theorem_linkage_obligation_discharged"] is True

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
        assert execution[key] is False, key


def test_psi_A_matter_exchange_attempt_execution_records_lean_status() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_EXECUTION
    assert (
        execution["full_toeformal_aggregate_status_for_execution"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_EXECUTION
    )
    assert (
        execution["scoped_lean_targets_status_for_execution"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
    )
    assert execution["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(execution)


def test_psi_A_matter_exchange_attempt_execution_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_EXECUTION_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_EXECUTION_TARGET in registry["completed_targets"]
    assert CONSUMED_EXECUTION_TARGET in registry["consumed_targets"]
    assert CONSUMED_EXECUTION_TARGET in registry["paused_lanes"]
    if is_current:
        assert NEXT_TARGET not in registry["paused_lanes"]
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    executed = workstream(CONSUMED_EXECUTION_TARGET, registry)
    assert executed["status"] == "paused"
    assert executed["authorization_evidence"] == evidence
    assert executed["report"] == _rel(DEFAULT_OUT)
    assert executed["execution_result"] == OUTCOME_ID
    assert executed["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert executed["selected_next_target"] == NEXT_TARGET
    assert executed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert executed["proof_attempt_executed"] == "yes"
    assert executed["theorem_discharged"] == "yes"
    assert executed["rule_promoted"] == "no"
    assert executed["master_action_promoted"] == "no"

    if is_current:
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["report"] == _rel(DEFAULT_OUT)
        assert active["consumed_target"] == CONSUMED_EXECUTION_TARGET
        assert active["execution_result"] == OUTCOME_ID
        assert active["strict_execution_result"] == STRICT_EXECUTION_RESULT
        assert active["review_result"] == "PENDING"
        assert active["proof_attempt_executed"] == "yes"
        assert active["theorem_discharged"] == "yes"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        reviewed = workstream(NEXT_TARGET, registry)
        assert reviewed["status"] == "paused"
        assert reviewed["execution_result"] == OUTCOME_ID
        assert reviewed["strict_execution_result"] == STRICT_EXECUTION_RESULT
        assert reviewed["proof_attempt_executed"] == "yes"
        assert reviewed["theorem_discharged"] == "yes"
        assert reviewed["rule_promoted"] == "no"

        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] in {
            CLOSEOUT_PREPARATION_TARGET,
            CLOSEOUT_REVIEW_TARGET,
            POST_CLOSEOUT_SELECTOR_TARGET,
            POST_SELECTOR_REVIEW_TARGET,
            POST_SELECTOR_PACKET_TARGET,
            POST_SELECTOR_PACKET_REVIEW_TARGET,
        }
        assert active["consumed_target"] in {
            NEXT_TARGET,
            CLOSEOUT_PREPARATION_TARGET,
            CLOSEOUT_REVIEW_TARGET,
            POST_CLOSEOUT_SELECTOR_TARGET,
            POST_SELECTOR_REVIEW_TARGET,
            POST_SELECTOR_PACKET_TARGET,
        }
        if active["workstream_id"] == CLOSEOUT_PREPARATION_TARGET:
            assert active["execution_result"] == OUTCOME_ID
        elif active["workstream_id"] == CLOSEOUT_REVIEW_TARGET:
            assert active["closeout_result"] == (
                "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSED_AS_DIRAC_"
                "PAIR_LINKED_MATTER_EXCHANGE_ROUTE_NO_CK_RULE_PROMOTION_OR_SEAM_CLOSURE"
            )
        elif active["workstream_id"] == POST_CLOSEOUT_SELECTOR_TARGET:
            assert active["review_result"] == (
                "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_"
                "REVIEW_ACCEPTS_DIRAC_PAIR_LINKED_MATTER_EXCHANGE_ROUTE_NO_CK_RULE_"
                "PROMOTION_OR_SEAM_CLOSURE"
            )
        elif active["workstream_id"] == POST_SELECTOR_REVIEW_TARGET:
            assert active["selection_result"] == POST_SELECTOR_OUTCOME
            assert active["review_result"] == "PENDING"
        else:
            assert active["workstream_id"] in {
                POST_SELECTOR_PACKET_TARGET,
                POST_SELECTOR_PACKET_REVIEW_TARGET,
            }
            if active["workstream_id"] == POST_SELECTOR_PACKET_TARGET:
                assert active["consumed_target"] == POST_SELECTOR_REVIEW_TARGET
            else:
                assert active["consumed_target"] == POST_SELECTOR_PACKET_TARGET
                assert active["review_result"] == "PENDING"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"


def test_psi_A_matter_exchange_attempt_execution_mirrors() -> None:
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
        STRICT_EXECUTION_RESULT,
        PACKET_CLASSIFICATION,
        "PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairExecution",
        CONSUMED_EXECUTION_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        TARGET,
        THEOREM_TARGET_STATEMENT,
        DIRAC_EQUATION_SHAPE,
        ADJOINT_DIRAC_EQUATION_SHAPE,
        CURRENT_DEFINITION,
        ROUTE_STATEMENT,
        LEAN_STATUS_WORDING_FOR_EXECUTION,
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION_OUTCOME_v0",
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_EXECUTION_NONCLAIM_BOUNDARY_v0",
        "psi_A_matter_exchange_from_dirac_pair_cancellations",
        "matter exchange route constructed from the Dirac-pair route",
        "no C_k rule promotion",
        "no C_k action embedding",
        "no C_k action variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
        "working-form, noncanonical",
    ]:
        assert token in joined, token


def test_psi_A_matter_exchange_attempt_execution_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution_gate.py"
    )
