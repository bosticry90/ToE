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
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_execution_report import (
    DEFAULT_OUT as EXECUTION_OUT,
    LEAN_PACKET_PATH as EXECUTION_LEAN_PACKET_PATH,
    OUTCOME_ID as EXECUTION_OUTCOME,
    STRICT_EXECUTION_RESULT,
)
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    C_SOURCE_A_RESIDUAL_DEFINITION,
    CLOSEOUT_OUTCOME,
    CLOSEOUT_STATEMENT,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LINKAGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    REVIEW_RESULT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SOURCE_ADMISSIBILITY_CONDITION,
    STRICT_REVIEW_RESULT,
    TARGET_CONCLUSION,
    build_A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review,
)
from formal.python.tools.A_source_theorem_linkage_obligation_closeout_report import (
    NEXT_TARGET as CLOSEOUT_REVIEW_TARGET,
    OUTCOME_ID as CLOSEOUT_RESULT,
    STRICT_CLOSEOUT_RESULT,
)
from formal.python.tools.A_source_theorem_linkage_obligation_closeout_result_review_report import (
    NEXT_TARGET as A_SOURCE_SELECTOR_TARGET,
    OUTCOME_ID as CLOSEOUT_REVIEW_RESULT,
    STRICT_REVIEW_RESULT as STRICT_CLOSEOUT_REVIEW_RESULT,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_A_source_closeout_report import (
    NEXT_TARGET as A_SOURCE_SELECTOR_REVIEW_TARGET,
    OUTCOME_ID as A_SOURCE_SELECTOR_OUTCOME,
    SELECTED_OBLIGATION as A_SOURCE_SELECTOR_SELECTED_OBLIGATION,
    STRICT_SELECTION_RESULT as STRICT_A_SOURCE_SELECTOR_OUTCOME,
)
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_A_source_closeout_result_review_report import (
    NEXT_TARGET as PHI_SOURCE_PACKET_TARGET,
    OUTCOME_ID as A_SOURCE_SELECTOR_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as STRICT_A_SOURCE_SELECTOR_REVIEW_OUTCOME,
)
from formal.python.tools.phi_source_theorem_linkage_obligation_packet_report import (
    NEXT_TARGET as PHI_SOURCE_PACKET_REVIEW_TARGET,
    OUTCOME_ID as PHI_SOURCE_PACKET_OUTCOME,
    STRICT_PACKET_RESULT as STRICT_PHI_SOURCE_PACKET_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review_report.py"
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


def _assert_A_source_selector_or_review_active(registry: dict, active: dict) -> None:
    if active["workstream_id"] == A_SOURCE_SELECTOR_TARGET:
        assert active["status"] == "active"
        assert active["consumed_target"] == CLOSEOUT_REVIEW_TARGET
        assert active["review_result"] == CLOSEOUT_REVIEW_RESULT
        assert active["selection_result"] == "PENDING"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
        return

    selector = _workstream(registry, A_SOURCE_SELECTOR_TARGET)
    assert selector["status"] == "paused"
    assert selector["selected_next_target"] == A_SOURCE_SELECTOR_REVIEW_TARGET
    assert selector["selection_result"] == A_SOURCE_SELECTOR_OUTCOME
    assert selector["strict_selection_result"] == STRICT_A_SOURCE_SELECTOR_OUTCOME
    assert selector["rule_promoted"] == "no"
    assert selector["master_action_promoted"] == "no"

    if active["workstream_id"] == A_SOURCE_SELECTOR_REVIEW_TARGET:
        assert active["status"] == "active"
        assert active["consumed_target"] == A_SOURCE_SELECTOR_TARGET
        assert active["selector_outcome"] == A_SOURCE_SELECTOR_OUTCOME
        assert active["strict_selector_outcome"] == STRICT_A_SOURCE_SELECTOR_OUTCOME
        assert active["review_result"] == "PENDING"
        assert active["selected_obligation"] == A_SOURCE_SELECTOR_SELECTED_OBLIGATION
        assert active["proof_execution_authorized"] == "no"
        assert active["gap_discharged"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
        return

    selector_review = _workstream(registry, A_SOURCE_SELECTOR_REVIEW_TARGET)
    assert selector_review["status"] == "paused"
    assert selector_review["review_result"] == A_SOURCE_SELECTOR_REVIEW_OUTCOME
    assert selector_review["strict_review_result"] == (
        STRICT_A_SOURCE_SELECTOR_REVIEW_OUTCOME
    )
    assert selector_review["selected_next_target"] == PHI_SOURCE_PACKET_TARGET
    assert selector_review["C_source_phi_discharged"] == "no"
    assert selector_review["proof_attempt_executed"] == "no"
    assert selector_review["rule_promoted"] == "no"
    assert selector_review["master_action_promoted"] == "no"

    if active["workstream_id"] == PHI_SOURCE_PACKET_TARGET:
        assert active["status"] == "active"
        assert active["consumed_target"] == A_SOURCE_SELECTOR_REVIEW_TARGET
        assert active["review_result"] == A_SOURCE_SELECTOR_REVIEW_OUTCOME
        assert active["strict_review_result"] == STRICT_A_SOURCE_SELECTOR_REVIEW_OUTCOME
        assert active["packet_result"] == "PENDING"
        assert active["selected_obligation"] == A_SOURCE_SELECTOR_SELECTED_OBLIGATION
        assert active["proof_execution_authorized"] == "no"
        assert active["C_source_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["A_source_route_imported"] == "no"
        assert active["psi_A_sourced_Maxwell_imported"] == "no"
        assert active["QFT_GR_source_route_imported"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
        return

    phi_packet = _workstream(registry, PHI_SOURCE_PACKET_TARGET)
    assert phi_packet["status"] == "paused"
    assert phi_packet["packet_result"] == PHI_SOURCE_PACKET_OUTCOME
    assert phi_packet["strict_packet_result"] == STRICT_PHI_SOURCE_PACKET_OUTCOME
    assert phi_packet["selected_next_target"] == PHI_SOURCE_PACKET_REVIEW_TARGET
    assert phi_packet["C_source_phi_discharged"] == "no"
    assert phi_packet["A_source_route_imported"] == "no"
    assert phi_packet["psi_A_sourced_Maxwell_imported"] == "no"
    assert phi_packet["QFT_GR_source_route_imported"] == "no"
    assert phi_packet["rule_promoted"] == "no"
    assert phi_packet["master_action_promoted"] == "no"

    assert active["status"] == "active"
    assert active["workstream_id"] == PHI_SOURCE_PACKET_REVIEW_TARGET
    assert active["consumed_target"] == PHI_SOURCE_PACKET_TARGET
    assert active["packet_result"] == PHI_SOURCE_PACKET_OUTCOME
    assert active["strict_packet_result"] == STRICT_PHI_SOURCE_PACKET_OUTCOME
    assert active["review_result"] == "PENDING"
    assert active["selected_obligation"] == A_SOURCE_SELECTOR_SELECTED_OBLIGATION
    assert active["proof_execution_authorized"] == "no"
    assert active["C_source_phi_discharged"] == "no"
    assert active["phi_sector_closure_claimed"] == "no"
    assert active["A_source_route_imported"] == "no"
    assert active["psi_A_sourced_Maxwell_imported"] == "no"
    assert active["QFT_GR_source_route_imported"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def consumed_target() -> str:
    return "review_A_source_theorem_linkage_attempt_from_standalone_A_route_result"


def test_A_source_execution_result_review_files_exist() -> None:
    for path in [
        EXECUTION_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        EXECUTION_LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_A_source_execution_result_review_accepts_constructed_linkage() -> None:
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
    assert review["closeout_outcome"] == CLOSEOUT_OUTCOME
    assert review["closeout_statement"] == CLOSEOUT_STATEMENT
    assert (
        build_A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review()
        == review
    )


def test_A_source_execution_result_review_records_route_and_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["C_source_A_residual_definition"] == C_SOURCE_A_RESIDUAL_DEFINITION
    assert review["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert review["target_conclusion"] == TARGET_CONCLUSION
    assert review["execution_route"] == LINKAGE_ROUTE
    assert review["linkage_route"] == LINKAGE_ROUTE
    assert review["plain_meaning"] == PLAIN_MEANING
    assert review["definition_linkage_constructed"] is True
    assert review["C_source_A_zero_derived"] is True
    assert review["review_executes_attempt"] is False
    assert review["proof_execution_authorized"] is False
    assert review["proof_attempt_executed"] is True
    assert review["theorem_discharged"] is True
    assert review["theorem_linkage_completed"] is True
    assert review["closeout_preparation_authorized"] is True

    for key in [
        "J_current_imported",
        "psi_A_sourced_route_substituted",
        "sourced_Maxwell_route_substituted",
        "A_sector_closure_claimed",
        "sourced_maxwell_closure_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_A_source_execution_result_review_records_lean_status() -> None:
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


def test_A_source_execution_result_review_rotates_to_closeout_preparation() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    report = _rel(DEFAULT_OUT)

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=consumed_target(),
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["execution_result"] == EXECUTION_OUTCOME
    assert consumed["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["C_source_A_zero_derived"] == "yes"
    assert consumed["J_current_imported"] == "no"
    assert consumed["psi_A_sourced_route_substituted"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = active_workstream(registry)
    if is_current:
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["report"] == report
        assert active["consumed_target"] == consumed_target()
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["closeout_outcome_suggested"] == CLOSEOUT_OUTCOME
        assert active["closeout_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["C_source_A_zero_derived"] == "yes"
        assert active["J_current_imported"] == "no"
        assert active["psi_A_sourced_route_substituted"] == "no"
        assert active["sourced_maxwell_closure_claimed"] == "no"
        assert active["full_maxwell_closure_claimed"] == "no"
        assert active["A_sector_closure_claimed"] == "no"
        assert active["seam_closure_claim"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        closeout = _workstream(registry, NEXT_TARGET)
        assert closeout["status"] == "paused"
        assert closeout["closeout_result"] == CLOSEOUT_RESULT
        assert closeout["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
        assert closeout["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
        assert closeout["A_source_theorem_linkage_obligation_locally_closed"] == "yes"
        assert closeout["J_current_imported"] == "no"
        assert closeout["psi_A_sourced_route_substituted"] == "no"
        assert closeout["sourced_maxwell_closure_claimed"] == "no"
        assert closeout["full_maxwell_closure_claimed"] == "no"
        assert closeout["A_sector_closure_claimed"] == "no"
        assert closeout["seam_closure_claim"] == "no"
        assert closeout["rule_promoted"] == "no"
        assert closeout["master_action_promoted"] == "no"

        if active["workstream_id"] == CLOSEOUT_REVIEW_TARGET:
            assert active["status"] == "active"
            assert active["consumed_target"] == NEXT_TARGET
            assert active["closeout_result"] == CLOSEOUT_RESULT
            assert active["review_result"] == "PENDING"
        else:
            closeout_review = _workstream(registry, CLOSEOUT_REVIEW_TARGET)
            assert closeout_review["status"] == "paused"
            assert closeout_review["review_result"] == CLOSEOUT_REVIEW_RESULT
            assert closeout_review["strict_review_result"] == (
                STRICT_CLOSEOUT_REVIEW_RESULT
            )
            assert closeout_review["selected_next_target"] == A_SOURCE_SELECTOR_TARGET

            _assert_A_source_selector_or_review_active(registry, active)


def test_A_source_execution_result_review_mirrors() -> None:
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
        "ASourceTheoremLinkageAttemptFromStandaloneARouteExecutionResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        CLOSEOUT_OUTCOME,
        CLOSEOUT_STATEMENT,
        C_SOURCE_A_RESIDUAL_DEFINITION,
        SOURCE_ADMISSIBILITY_CONDITION,
        TARGET_CONCLUSION,
        PLAIN_MEANING,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_RESULT_REVIEW_OUTCOME_v0",
        "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "standalone A-source theorem-linkage route constructed",
        "C_source^{A,nu} = 0 locally linked",
        "no J current imported",
        "no psi-A sourced Maxwell substitution",
        "no A-sector closure",
        "no full Maxwell closure",
        "no C_k promotion",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_A_source_execution_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review_gate.py"
    )
