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
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_report import (
    BOUNDARY_ITEMS,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    DEFAULT_OUT,
    EXECUTION_FINDINGS,
    EXECUTION_REDUCTION_ROUTE,
    EXECUTION_RESULT,
    EXECUTION_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    ON_SHELL_CONDITION,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_PURITY_WATCH_ITEMS,
    SCHEMA_ID,
    STRICT_EXECUTION_RESULT,
    STRICT_SUGGESTED_REVIEW_OUTCOME,
    SUGGESTED_REVIEW_OUTCOME,
    TARGET_CONCLUSION,
    build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as RESULT_REVIEW_LEAN_PACKET_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_result_review_report import (
    CLOSEOUT_OUTCOME,
    DEFAULT_OUT as EXECUTION_RESULT_REVIEW_OUT,
    LEAN_PACKET_PATH as EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as CLOSEOUT_TARGET,
    OUTCOME_ID as EXECUTION_RESULT_REVIEW_OUTCOME,
    STRICT_CLOSEOUT_OUTCOME,
    STRICT_REVIEW_RESULT as EXECUTION_RESULT_REVIEW_STRICT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_report.py"
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
    return "execute_phi_source_theorem_linkage_attempt_from_standalone_phi_route"


def prior_review_target() -> str:
    return "review_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result"


def test_phi_source_standalone_attempt_execution_files_exist() -> None:
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


def test_phi_source_standalone_attempt_execution_report_matches_builder() -> None:
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
        build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution()
        == execution
    )


def test_phi_source_standalone_attempt_execution_constructs_linkage() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["execution_findings"] == EXECUTION_FINDINGS
    assert execution["boundary_items"] == BOUNDARY_ITEMS
    assert execution["route_purity_watch_items"] == ROUTE_PURITY_WATCH_ITEMS
    assert execution["selected_obligation"] == "C_source^phi theorem-linkage obligation"
    assert execution["selected_theorem_linkage_gap"] == (
        "C_source^phi theorem-linkage gap"
    )
    assert execution["selected_obligation_row_id"] == "C_source^phi"
    assert execution["C_source_phi_residual_definition"] == (
        C_SOURCE_PHI_RESIDUAL_DEFINITION
    )
    assert execution["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert execution["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert execution["on_shell_condition"] == ON_SHELL_CONDITION
    assert execution["target_conclusion"] == TARGET_CONCLUSION
    assert execution["execution_route"] == EXECUTION_ROUTE
    assert execution["execution_reduction_route"] == EXECUTION_REDUCTION_ROUTE
    assert execution["plain_meaning"] == PLAIN_MEANING
    assert execution["lean_theorem_name"] == LEAN_THEOREM_NAME
    assert execution["C_source_phi_zero_constructed"] is True
    assert execution["C_source_phi_zero_derived"] is True
    assert execution["C_source_phi_linkage_constructed"] is True
    assert execution["definition_linkage_constructed"] is True
    assert execution["theorem_linkage_completed"] is True


def test_phi_source_standalone_attempt_execution_blocks_imports_and_closures() -> None:
    execution = _json(DEFAULT_OUT)
    route_text = " ".join(execution["execution_route"])

    assert "J^alpha" not in route_text
    assert "nabla_mu F" not in route_text
    assert "QFT-GR" not in route_text
    assert execution["A_source_route_imported"] is False
    assert execution["A_sector_route_imported"] is False
    assert execution["psi_A_sourced_Maxwell_imported"] is False
    assert execution["QFT_GR_source_route_imported"] is False
    assert execution["J_current_imported"] is False

    assert execution["proof_execution_authorized"] is True
    assert execution["proof_attempt_executed"] is True
    assert execution["theorem_execution_authorized"] is True
    assert execution["theorem_discharged"] is True
    assert execution["theorem_linkage_obligation_discharged"] is True
    assert execution["phi_source_theorem_linkage_obligation_discharged"] is True
    assert execution["C_source_phi_discharged"] is True
    assert execution["C_source_phi_admissibility_status"] == (
        "local theorem-linkage only"
    )

    for key in [
        "C_source_phi_closure_claimed",
        "phi_sector_closure_claimed",
        "full_scalar_qft_closure_claimed",
        "full_scalar_QFT_closure_claimed",
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


def test_phi_source_standalone_attempt_execution_records_lean_status() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_EXECUTION
    assert (
        execution["full_toeformal_aggregate_status_for_execution"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert execution["scoped_lean_targets_status_for_execution"] == (
        "PASSED_SERIAL_RERUN"
    )
    assert execution["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(execution)


def test_phi_source_standalone_attempt_execution_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    report = _rel(DEFAULT_OUT)

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
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["C_source_phi_zero_derived"] == "yes"
    assert consumed["C_source_phi_linkage_constructed"] == "yes"
    assert consumed["C_source_phi_discharged"] == "yes"
    assert consumed["phi_sector_closure_claimed"] == "no"
    assert consumed["full_scalar_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["report"] == report
        assert active["consumed_target"] == consumed_target()
        assert active["consumed_target_kind"] == (
            "phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution"
        )
        assert active["execution_result"] == OUTCOME_ID
        assert active["strict_execution_result"] == STRICT_EXECUTION_RESULT
        assert active["review_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["C_source_phi_zero_derived"] == "yes"
        assert active["C_source_phi_linkage_constructed"] == "yes"
        assert active["C_source_phi_discharged"] == "yes"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["em_qft_closure_claimed"] == "no"
        assert active["general_C_k_closure"] == "no"
        assert active["seam_closure_claim"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
        assert active["result_review_outcome_suggested"] == SUGGESTED_REVIEW_OUTCOME
        assert active["strict_result_review_outcome_suggested"] == (
            STRICT_SUGGESTED_REVIEW_OUTCOME
        )
    else:
        review = _workstream(registry, NEXT_TARGET)
        assert review["status"] == "paused"
        assert review["authorization_evidence"] == _rel(
            EXECUTION_RESULT_REVIEW_LEAN_PACKET_PATH
        )
        assert review["report"] == _rel(EXECUTION_RESULT_REVIEW_OUT)
        assert review["review_result"] == EXECUTION_RESULT_REVIEW_OUTCOME
        assert review["strict_review_result"] == EXECUTION_RESULT_REVIEW_STRICT_OUTCOME
        assert review["selected_next_target"] == CLOSEOUT_TARGET
        assert review["C_source_phi_zero_derived"] == "yes"
        assert review["phi_sector_closure_claimed"] == "no"
        assert review["full_scalar_qft_closure_claimed"] == "no"
        assert review["qft_gr_closure_claimed"] == "no"
        assert review["em_qft_closure_claimed"] == "no"
        assert review["general_C_k_closure"] == "no"
        assert review["seam_closure_claim"] == "no"
        assert review["rule_promoted"] == "no"
        assert review["master_action_promoted"] == "no"

        active = active_workstream(registry)
        if active["workstream_id"] == CLOSEOUT_TARGET:
            assert active["status"] == "active"
            assert active["consumed_target"] == NEXT_TARGET
            assert active["review_result"] == EXECUTION_RESULT_REVIEW_OUTCOME
            assert active["strict_review_result"] == (
                EXECUTION_RESULT_REVIEW_STRICT_OUTCOME
            )
            assert active["closeout_outcome_suggested"] == CLOSEOUT_OUTCOME
            assert active["strict_closeout_outcome_suggested"] == (
                STRICT_CLOSEOUT_OUTCOME
            )
            assert active["closeout_result"] == "PENDING"
            assert active["rule_promoted"] == "no"
            assert active["master_action_promoted"] == "no"


def test_phi_source_standalone_attempt_execution_mirrors() -> None:
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
        "PhiSourceTheoremLinkageAttemptFromStandalonePhiRouteExecution",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_REVIEW_OUTCOME,
        STRICT_SUGGESTED_REVIEW_OUTCOME,
        C_SOURCE_PHI_RESIDUAL_DEFINITION,
        RESIDUAL_IDENTITY_FORM,
        ON_SHELL_RESIDUAL_FORM,
        ON_SHELL_CONDITION,
        TARGET_CONCLUSION,
        PLAIN_MEANING,
        LEAN_THEOREM_NAME,
        LEAN_STATUS_WORDING_FOR_EXECUTION,
        "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_OUTCOME_v0",
        "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTION_NONCLAIM_BOUNDARY_v0",
        "standalone phi-source theorem-linkage attempt executed",
        "C_source^nu[g, phi] definition preserved",
        "scalar/on-shell residual identity used",
        "R_i^phi = 0 applied as on-shell condition",
        "C_source^nu[g, phi] = 0 locally constructed",
        "no phi-sector closure",
        "no full scalar/QFT closure",
        "no QFT-GR closure",
        "no EM-QFT closure",
        "no general C_k closure",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no empirical validation",
        "no master-action promotion",
        "no seam closure",
    ]:
        assert token in joined, token


def test_phi_source_standalone_attempt_execution_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution_gate.py"
    )
