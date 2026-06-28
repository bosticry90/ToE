from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    CLOSEOUT_OUTCOME,
    CLOSEOUT_STATEMENT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EXECUTION_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GAUGE_EXCHANGE_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    REVIEW_RESULT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_result_review,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_closeout_report import (
    DEFAULT_OUT as CLOSEOUT_OUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    NEXT_TARGET as CLOSEOUT_REVIEW_TARGET,
    NEXT_TARGET_KIND as CLOSEOUT_REVIEW_TARGET_KIND,
    OUTCOME_ID as CLOSEOUT_RESULT,
    STRICT_CLOSEOUT_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_result_review_report.py"
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


def test_psi_A_total_conservation_execution_result_review_files_exist() -> None:
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


def test_psi_A_total_conservation_execution_result_review_accepts_bridge() -> None:
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
        build_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_result_review()
        == review
    )


def test_psi_A_total_conservation_execution_result_review_records_scope() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["claim_boundary"] == "theorem-linkage result review only, not physics closure"
    assert review["input_route"] == (
        "accepted gauge-sector exchange route plus accepted matter-sector exchange route"
    )
    assert review["proof_style"] == PROOF_STYLE
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["gauge_exchange_route"] == GAUGE_EXCHANGE_ROUTE
    assert review["matter_exchange_route"] == MATTER_EXCHANGE_ROUTE
    assert review["total_stress_energy_definition"] == TOTAL_STRESS_ENERGY_DEFINITION
    assert review["total_conservation_conclusion"] == TOTAL_CONSERVATION_CONCLUSION
    assert review["plain_meaning"] == PLAIN_MEANING
    assert review["exchange_cancellation_route_constructed"] is True
    assert review["total_conservation_derived"] is True
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


def test_psi_A_total_conservation_execution_result_review_records_lean_status() -> None:
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


def test_psi_A_total_conservation_execution_result_review_rotates_to_closeout() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    closeout_evidence = _rel(CLOSEOUT_LEAN_PACKET_PATH)
    closeout_report = _rel(CLOSEOUT_OUT)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert CLOSEOUT_REVIEW_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CLOSEOUT_REVIEW_TARGET in registry["next_strict_target_coverage"]

    reviewed = _workstream(registry, CONSUMED_TARGET)
    assert reviewed["status"] == "paused"
    assert reviewed["authorization_evidence"] == evidence
    assert reviewed["report"] == _rel(DEFAULT_OUT)
    assert reviewed["review_result"] == OUTCOME_ID
    assert reviewed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert reviewed["selected_next_target"] == NEXT_TARGET
    assert reviewed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert reviewed["review_executes_attempt"] == "no"
    assert reviewed["proof_attempt_executed"] == "yes"
    assert reviewed["theorem_discharged"] == "yes"
    assert reviewed["rule_promoted"] == "no"
    assert reviewed["master_action_promoted"] == "no"

    closeout = _workstream(registry, NEXT_TARGET)
    assert closeout["status"] == "paused"
    assert closeout["authorization_evidence"] == closeout_evidence
    assert closeout["report"] == closeout_report
    assert closeout["closeout_result"] == CLOSEOUT_RESULT
    assert closeout["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert closeout["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
    assert closeout["selected_next_target_kind"] == CLOSEOUT_REVIEW_TARGET_KIND
    assert closeout["local_psi_A_total_conservation_obligation_closed"] == "yes"
    assert closeout["rule_promoted"] == "no"
    assert closeout["master_action_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == (
        "review_ck_family_theorem_linkage_obligation_selection_after_"
        "psi_A_total_conservation_closeout_result"
    )
    assert active["consumed_target"] == (
        "select_next_ck_family_theorem_linkage_obligation_after_"
        "psi_A_total_conservation_closeout"
    )
    assert active["selection_result"] == (
        "CK_FAMILY_THEOREM_LINKAGE_OBLIGATION_SELECTION_AFTER_PSI_A_TOTAL_"
        "CONSERVATION_CLOSEOUT_SELECTS_PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_"
        "GAP_NO_PROOF_EXECUTION_OR_MASTER_ACTION_PROMOTION"
    )
    assert active["review_result"] == "PENDING"
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_total_conservation_execution_result_review_mirrors() -> None:
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
        "PsiATotalConservationTheoremLinkageAttemptFromExchangeRoutesExecutionResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        CLOSEOUT_OUTCOME,
        CLOSEOUT_STATEMENT,
        THEOREM_TARGET_STATEMENT,
        TOTAL_CONSERVATION_CONCLUSION,
        GAUGE_EXCHANGE_ROUTE,
        MATTER_EXCHANGE_ROUTE,
        TOTAL_STRESS_ENERGY_DEFINITION,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_ATTEMPT_FROM_EXCHANGE_ROUTES_EXECUTION_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "exchange-cancellation route constructed",
        "accepted gauge-sector exchange route used",
        "accepted matter-sector exchange route used",
        "no C_k promotion",
        "no action embedding",
        "no variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_total_conservation_execution_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_total_conservation_theorem_linkage_attempt_from_exchange_routes_execution_result_review_gate.py"
    )
