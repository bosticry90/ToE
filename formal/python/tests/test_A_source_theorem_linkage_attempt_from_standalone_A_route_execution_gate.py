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
    BOUNDARY_ITEMS,
    C_SOURCE_A_RESIDUAL_DEFINITION,
    DEFAULT_OUT,
    EXECUTION_FINDINGS,
    EXECUTION_RESULT,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    LINKAGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION,
    SOURCE_ADMISSIBILITY_CONDITION,
    STRICT_EXECUTION_RESULT,
    STRICT_SUGGESTED_REVIEW_OUTCOME,
    SUGGESTED_REVIEW_OUTCOME,
    TARGET_CONCLUSION,
    build_A_source_theorem_linkage_attempt_from_standalone_A_route_execution,
)
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
)
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review_report import (
    CLOSEOUT_OUTCOME,
    NEXT_TARGET as CLOSEOUT_TARGET,
    OUTCOME_ID as EXECUTION_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as EXECUTION_REVIEW_STRICT_OUTCOME,
)
from formal.python.tools.A_source_theorem_linkage_obligation_closeout_report import (
    NEXT_TARGET as CLOSEOUT_REVIEW_TARGET,
    OUTCOME_ID as CLOSEOUT_RESULT,
    STRICT_CLOSEOUT_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "A_source_theorem_linkage_attempt_from_standalone_A_route_execution_report.py"
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
    return "execute_A_source_theorem_linkage_attempt_from_standalone_A_route"


def prior_review_target() -> str:
    return "review_A_source_theorem_linkage_attempt_from_standalone_A_route_result"


def test_A_source_standalone_attempt_execution_files_exist() -> None:
    for path in [
        RESULT_REVIEW_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        RESULT_REVIEW_LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_A_source_standalone_attempt_execution_report_matches_builder() -> None:
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
    assert execution["consumed_target"] == consumed_target()
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert execution["suggested_review_outcome"] == SUGGESTED_REVIEW_OUTCOME
    assert execution["strict_suggested_review_outcome"] == (
        STRICT_SUGGESTED_REVIEW_OUTCOME
    )
    assert (
        build_A_source_theorem_linkage_attempt_from_standalone_A_route_execution()
        == execution
    )


def test_A_source_standalone_attempt_execution_constructs_linkage() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["execution_findings"] == EXECUTION_FINDINGS
    assert execution["boundary_items"] == BOUNDARY_ITEMS
    assert execution["selected_obligation"] == "C_source^A theorem-linkage obligation"
    assert execution["selected_theorem_linkage_gap"] == "C_source^A theorem-linkage gap"
    assert execution["selected_obligation_row_id"] == "C_source^A"
    assert execution["C_source_A_residual_definition"] == C_SOURCE_A_RESIDUAL_DEFINITION
    assert execution["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert execution["target_conclusion"] == TARGET_CONCLUSION
    assert execution["execution_route"] == LINKAGE_ROUTE
    assert execution["plain_meaning"] == PLAIN_MEANING
    assert execution["lean_theorem_name"] == LEAN_THEOREM_NAME
    assert execution["C_source_A_zero_constructed"] is True
    assert execution["C_source_A_zero_derived"] is True
    assert execution["definition_linkage_constructed"] is True
    assert execution["theorem_linkage_completed"] is True


def test_A_source_standalone_attempt_execution_blocks_imports_and_closures() -> None:
    execution = _json(DEFAULT_OUT)
    route_text = " ".join(execution["execution_route"])

    assert execution["J_current_imported"] is False
    assert execution["psi_A_sourced_maxwell_route"] == PSI_A_SOURCED_MAXWELL_ROUTE
    assert execution["psi_A_sourced_route_substituted"] is False
    assert execution["sourced_Maxwell_route_substituted"] is False
    assert "J^alpha" not in route_text
    assert "nabla_mu F^{mu alpha} = J^alpha" not in route_text

    assert execution["proof_execution_authorized"] is True
    assert execution["proof_attempt_executed"] is True
    assert execution["theorem_execution_authorized"] is True
    assert execution["theorem_discharged"] is True
    assert execution["theorem_linkage_obligation_discharged"] is True
    assert execution["A_source_theorem_linkage_obligation_discharged"] is True
    assert execution["C_source_A_discharged"] is True
    assert execution["C_source_A_closure_claimed"] is False
    assert execution["C_source_A_admissibility_status"] == "admissibility-only"

    for key in [
        "A_sector_closure_claimed",
        "sourced_maxwell_closure_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "general_C_k_closure",
        "C_k_dynamical_law_status",
        "C_k_rule_promoted",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "action_embedding_claimed",
        "action_variation_executed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert execution[key] is False, key


def test_A_source_standalone_attempt_execution_records_lean_status() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_EXECUTION
    assert (
        execution["full_toeformal_aggregate_status_for_execution"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert (
        execution["scoped_lean_targets_status_for_execution"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_EXECUTION
    )
    assert execution["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(execution)


def test_A_source_standalone_attempt_execution_rotates_to_result_review() -> None:
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

    assert prior_review_target() in registry["completed_targets"]
    assert prior_review_target() in registry["consumed_targets"]
    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["execution_result"] == OUTCOME_ID
    assert consumed["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["C_source_A_zero_derived"] == "yes"
    assert consumed["J_current_imported"] == "no"
    assert consumed["psi_A_sourced_route_substituted"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    active = active_workstream(registry)
    review = _workstream(registry, NEXT_TARGET)
    if is_current:
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["report"] == report
        assert active["consumed_target"] == consumed_target()
        assert active["result_review_outcome_suggested"] == SUGGESTED_REVIEW_OUTCOME
        assert active["strict_result_review_outcome_suggested"] == (
            STRICT_SUGGESTED_REVIEW_OUTCOME
        )
        assert active["execution_result"] == OUTCOME_ID
        assert active["review_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["C_source_A_zero_derived"] == "yes"
        assert active["J_current_imported"] == "no"
        assert active["psi_A_sourced_route_substituted"] == "no"
        assert active["sourced_maxwell_closure_claimed"] == "no"
        assert active["full_maxwell_closure_claimed"] == "no"
        assert active["A_sector_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"
        assert active["prior_result_review_outcome"] == RESULT_REVIEW_OUTCOME
    else:
        assert review["status"] == "paused"
        assert review["review_result"] == EXECUTION_REVIEW_OUTCOME
        assert review["strict_review_result"] == EXECUTION_REVIEW_STRICT_OUTCOME
        assert review["selected_next_target"] == CLOSEOUT_TARGET
        assert review["C_source_A_zero_derived"] == "yes"
        assert review["J_current_imported"] == "no"
        assert review["psi_A_sourced_route_substituted"] == "no"
        assert review["rule_promoted"] == "no"
        assert review["master_action_promoted"] == "no"

        if active["workstream_id"] == CLOSEOUT_TARGET:
            assert active["status"] == "active"
            assert active["consumed_target"] == NEXT_TARGET
            assert active["closeout_outcome_suggested"] == CLOSEOUT_OUTCOME
            assert active["closeout_result"] == "PENDING"
        else:
            closeout = _workstream(registry, CLOSEOUT_TARGET)
            assert closeout["status"] == "paused"
            assert closeout["closeout_result"] == CLOSEOUT_RESULT
            assert closeout["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
            assert closeout["selected_next_target"] == CLOSEOUT_REVIEW_TARGET
            assert closeout["A_source_theorem_linkage_obligation_locally_closed"] == "yes"
            assert closeout["J_current_imported"] == "no"
            assert closeout["psi_A_sourced_route_substituted"] == "no"
            assert closeout["rule_promoted"] == "no"
            assert closeout["master_action_promoted"] == "no"

            assert active["status"] == "active"
            assert active["workstream_id"] == CLOSEOUT_REVIEW_TARGET
            assert active["consumed_target"] == CLOSEOUT_TARGET
            assert active["closeout_result"] == CLOSEOUT_RESULT
            assert active["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
            assert active["review_result"] == "PENDING"


def test_A_source_standalone_attempt_execution_mirrors() -> None:
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
        "ASourceTheoremLinkageAttemptFromStandaloneARouteExecution",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_REVIEW_OUTCOME,
        STRICT_SUGGESTED_REVIEW_OUTCOME,
        C_SOURCE_A_RESIDUAL_DEFINITION,
        SOURCE_ADMISSIBILITY_CONDITION,
        TARGET_CONCLUSION,
        PLAIN_MEANING,
        LEAN_THEOREM_NAME,
        LEAN_STATUS_WORDING_FOR_EXECUTION,
        "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_OUTCOME_v0",
        "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_EXECUTION_NONCLAIM_BOUNDARY_v0",
        "no J current imported",
        "no psi-A sourced Maxwell substitution",
        "no sourced Maxwell closure",
        "no full Maxwell closure",
        "no A-sector closure",
        "no general C_k closure",
        "no action embedding",
        "no variation",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_A_source_standalone_attempt_execution_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_A_source_theorem_linkage_attempt_from_standalone_A_route_execution_gate.py"
    )
