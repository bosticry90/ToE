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
    DEFAULT_OUT as SELECTION_OUT,
    FOLLOW_ON_TARGET_AFTER_REVIEW as SELECTION_FOLLOW_ON_TARGET_AFTER_REVIEW,
    LEAN_PACKET_PATH as SELECTION_LEAN_PACKET_PATH,
    NEXT_TARGET as SELECTION_REVIEW_TARGET,
    OUTCOME_ID as SELECTION_OUTCOME,
    SELECTED_OBLIGATION as SELECTION_SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_RANK as SELECTION_SELECTED_OBLIGATION_RANK,
    STRICT_SELECTION_RESULT,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_closeout_report import (
    CLOSEOUT_RESULT,
    DEFAULT_OUT as CLOSEOUT_OUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
)
from formal.python.tools.psi_A_total_conservation_theorem_linkage_obligation_closeout_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    DEFAULT_OUT,
    FOLLOW_ON_TARGET_AFTER_SELECTOR_REVIEW,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GAUGE_EXCHANGE_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LIKELY_NEXT_OBLIGATION,
    LIKELY_SELECTOR_OUTCOME,
    MATTER_EXCHANGE_ROUTE,
    NEXT_OBLIGATION_REASON,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REVIEW_RESULT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    THEOREM_TARGET_STATEMENT,
    TOTAL_CONSERVATION_CONCLUSION,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_psi_A_total_conservation_theorem_linkage_obligation_closeout_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_total_conservation_theorem_linkage_obligation_closeout_result_review_report.py"
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
    return "review_psi_A_total_conservation_theorem_linkage_obligation_closeout_result"


def test_psi_A_total_conservation_closeout_result_review_files_exist() -> None:
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


def test_psi_A_total_conservation_closeout_result_review_accepts_closeout() -> None:
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
    assert (
        review["follow_on_target_after_selector_review"]
        == FOLLOW_ON_TARGET_AFTER_SELECTOR_REVIEW
    )
    assert review["likely_next_obligation"] == LIKELY_NEXT_OBLIGATION
    assert review["next_obligation_reason"] == NEXT_OBLIGATION_REASON
    assert (
        build_psi_A_total_conservation_theorem_linkage_obligation_closeout_result_review()
        == review
    )


def test_psi_A_total_conservation_closeout_result_review_preserves_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["closeout_outcome"] == CLOSEOUT_RESULT
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["gauge_exchange_route"] == GAUGE_EXCHANGE_ROUTE
    assert review["matter_exchange_route"] == MATTER_EXCHANGE_ROUTE
    assert review["total_stress_energy_definition"] == TOTAL_STRESS_ENERGY_DEFINITION
    assert review["total_conservation_conclusion"] == TOTAL_CONSERVATION_CONCLUSION
    assert review["exchange_cancellation_route_constructed"] is True
    assert review["total_conservation_derived"] is True
    assert review["watch_items_preserved"] is True
    assert review["local_psi_A_total_conservation_obligation_closed"] is True
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


def test_psi_A_total_conservation_closeout_result_review_records_lean_status() -> None:
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


def test_psi_A_total_conservation_closeout_result_review_rotates_to_selector() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    selection_evidence = _rel(SELECTION_LEAN_PACKET_PATH)

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
    assert registry["PREVIOUS_LIVE_NEXT_TARGET_v0"] == NEXT_TARGET
    assert registry["CURRENT_LIVE_NEXT_TARGET_v0"] == SELECTION_REVIEW_TARGET
    assert registry["ACTIVE_LANE_v0"] == SELECTION_REVIEW_TARGET
    assert registry["CURRENT_LIVE_TARGET_EVIDENCE_v0"] == selection_evidence
    assert registry["CURRENT_LIVE_TARGET_REPORT_v0"] == _rel(SELECTION_OUT)
    assert registry["CURRENT_LIVE_TARGET_OUTCOME_v0"] == SELECTION_OUTCOME
    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert SELECTION_REVIEW_TARGET not in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert SELECTION_REVIEW_TARGET in registry["next_strict_target_coverage"]

    closeout = _workstream(
        registry,
        "prepare_psi_A_total_conservation_theorem_linkage_obligation_closeout",
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
    assert consumed["local_psi_A_total_conservation_obligation_closed"] == "yes"
    assert consumed["general_C_k_theorem_linkage_closure"] == "no"
    assert consumed["C_k_dynamical_law_status"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert active["workstream_id"] == SELECTION_REVIEW_TARGET
    assert active["active_lane"] == SELECTION_REVIEW_TARGET
    assert active["authorization_evidence"] == selection_evidence
    assert active["authorized_next_strict_target"] == SELECTION_REVIEW_TARGET
    assert active["consumed_target"] == NEXT_TARGET
    assert active["packet_result"] == SELECTION_OUTCOME
    assert active["selection_result"] == SELECTION_OUTCOME
    assert active["strict_selection_result"] == STRICT_SELECTION_RESULT
    assert active["review_result"] == "PENDING"
    assert active["selected_next_target"] == SELECTION_FOLLOW_ON_TARGET_AFTER_REVIEW
    assert active["selected_obligation"] == SELECTION_SELECTED_OBLIGATION
    assert active["selected_obligation_rank"] == SELECTION_SELECTED_OBLIGATION_RANK
    assert active["proof_execution_authorized"] == "no"
    assert active["proof_attempt_executed"] == "no"
    assert active["theorem_discharged"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def test_psi_A_total_conservation_closeout_result_review_mirrors() -> None:
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
        "PsiATotalConservationTheoremLinkageObligationCloseoutResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_SELECTOR_OUTCOME,
        LIKELY_NEXT_OBLIGATION,
        FOLLOW_ON_TARGET_AFTER_SELECTOR_REVIEW,
        NEXT_OBLIGATION_REASON,
        THEOREM_TARGET_STATEMENT,
        TOTAL_STRESS_ENERGY_DEFINITION,
        TOTAL_CONSERVATION_CONCLUSION,
        GAUGE_EXCHANGE_ROUTE,
        MATTER_EXCHANGE_ROUTE,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_TOTAL_CONSERVATION_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "psi-A total conservation theorem-linkage obligation locally closed",
        "psi-A matter-sector exchange theorem-linkage gap",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no general C_k closure",
        "no C_k dynamical-law status",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_total_conservation_closeout_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_total_conservation_theorem_linkage_obligation_closeout_result_review_gate.py"
    )
