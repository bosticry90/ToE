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
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_closeout_report import (
    CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    GAUGE_EXCHANGE_ROUTE,
    INPUT_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LIKELY_NEXT_OBLIGATION,
    LIKELY_NEXT_OBLIGATION_REASON,
    LIKELY_NEXT_SELECTOR_TARGET,
    MATTER_EXCHANGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NONCLAIMS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PROOF_STYLE,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_CLOSEOUT,
    STRICT_CLOSEOUT_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_psi_A_total_conservation_theorem_linkage_obligation_closeout,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_closeout_result_review_report import (
    DEFAULT_OUT as REVIEW_OUT,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as SELECTOR_TARGET,
    NEXT_TARGET_KIND as SELECTOR_TARGET_KIND,
    OUTCOME_ID as REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_total_conservation_theorem_linkage_obligation_closeout_report.py"
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


def test_psi_A_total_conservation_closeout_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_total_conservation_closeout_accepts_local_exchange_cancellation() -> None:
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
    assert build_psi_A_total_conservation_theorem_linkage_obligation_closeout() == closeout


def test_psi_A_total_conservation_closeout_records_claims_and_nonclaims() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["closeout_claims"] == CLOSEOUT_CLAIMS
    assert closeout["nonclaims"] == NONCLAIMS
    assert closeout["claim_boundary"] == CLAIM_BOUNDARY
    assert closeout["input_route"] == INPUT_ROUTE
    assert closeout["proof_style"] == PROOF_STYLE
    assert closeout["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert closeout["gauge_exchange_route"] == GAUGE_EXCHANGE_ROUTE
    assert closeout["matter_exchange_route"] == MATTER_EXCHANGE_ROUTE
    assert closeout["total_stress_energy_definition"] == TOTAL_STRESS_ENERGY_DEFINITION
    assert closeout["total_conservation_conclusion"] == TOTAL_CONSERVATION_CONCLUSION
    assert closeout["exchange_cancellation_route_constructed"] is True
    assert closeout["total_conservation_derived"] is True
    assert closeout["T_total_definition_used"] is True
    assert closeout["watch_items_preserved"] is True
    assert closeout["local_psi_A_total_conservation_obligation_closed"] is True
    assert closeout["psi_A_total_conservation_obligation_locally_closed"] is True
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
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert closeout[key] is False, key


def test_psi_A_total_conservation_closeout_records_lean_status() -> None:
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


def test_psi_A_total_conservation_closeout_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    review_evidence = _rel(REVIEW_LEAN_PACKET_PATH)
    review_report = _rel(REVIEW_OUT)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["consumed_targets"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert SELECTOR_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["local_psi_A_total_conservation_obligation_closed"] == "yes"
    assert consumed["general_C_k_theorem_linkage_closure"] == "no"
    assert consumed["C_k_dynamical_law_status"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    review = _workstream(registry, NEXT_TARGET)
    assert review["status"] == "paused"
    assert review["authorization_evidence"] == review_evidence
    assert review["report"] == review_report
    assert review["review_result"] == REVIEW_OUTCOME
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["selected_next_target"] == SELECTOR_TARGET
    assert review["selected_next_target_kind"] == SELECTOR_TARGET_KIND
    assert review["local_psi_A_total_conservation_obligation_closed"] == "yes"
    assert review["general_C_k_theorem_linkage_closure"] == "no"
    assert review["C_k_dynamical_law_status"] == "no"
    assert review["rule_promoted"] == "no"
    assert review["master_action_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == SELECTOR_TARGET
    assert active["active_lane"] == SELECTOR_TARGET
    assert active["authorization_evidence"] == review_evidence
    assert active["authorized_next_strict_target"] == SELECTOR_TARGET
    assert active["consumed_target"] == NEXT_TARGET
    assert active["packet_result"] == REVIEW_OUTCOME
    assert active["review_result"] == REVIEW_OUTCOME
    assert active["selection_result"] == "PENDING"
    assert active["selected_next_target"] == SELECTOR_TARGET
    assert active["selected_next_target_kind"] == SELECTOR_TARGET_KIND
    assert active["likely_next_obligation"] == LIKELY_NEXT_OBLIGATION
    assert active["proof_execution_authorized"] == "no"
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_total_conservation_closeout_mirrors() -> None:
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
        "PsiATotalConservationTheoremLinkageObligationCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_NEXT_SELECTOR_TARGET,
        LIKELY_NEXT_OBLIGATION,
        CLOSEOUT_STATEMENT,
        THEOREM_TARGET_STATEMENT,
        TOTAL_STRESS_ENERGY_DEFINITION,
        TOTAL_CONSERVATION_CONCLUSION,
        GAUGE_EXCHANGE_ROUTE,
        MATTER_EXCHANGE_ROUTE,
        LEAN_STATUS_WORDING_FOR_CLOSEOUT,
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_OUTCOME_v0",
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "psi-A total conservation theorem-linkage obligation locally closed",
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


def test_psi_A_total_conservation_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_total_conservation_theorem_linkage_obligation_closeout_gate.py"
    )
