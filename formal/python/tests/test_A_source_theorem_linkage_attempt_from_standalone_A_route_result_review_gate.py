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
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_report import (
    DEFAULT_OUT as ATTEMPT_OUT,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    STRICT_ATTEMPT_PREPARATION_RESULT,
)
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    BLOCKED_CLAIMS,
    C_SOURCE_A_RESIDUAL_DEFINITION,
    DEFAULT_OUT,
    EXECUTION_ROUTE_TO_AUTHORIZE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LINKAGE_ROUTE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    STANDALONE_A_ROUTE,
    STRICT_REVIEW_RESULT,
    STRICT_SUGGESTED_EXECUTION_OUTCOME,
    SUGGESTED_EXECUTION_OUTCOME,
    TARGET_CONCLUSION,
    WATCH_ITEMS,
    build_A_source_theorem_linkage_attempt_from_standalone_A_route_result_review,
)
from formal.python.tools.A_source_theorem_linkage_attempt_from_standalone_A_route_execution_result_review_report import (
    CLOSEOUT_OUTCOME,
    DEFAULT_OUT as EXECUTION_REVIEW_OUT,
    LEAN_PACKET_PATH as EXECUTION_REVIEW_LEAN_PACKET_PATH,
    NEXT_TARGET as CLOSEOUT_TARGET,
    OUTCOME_ID as EXECUTION_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as EXECUTION_REVIEW_STRICT_OUTCOME,
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
from formal.python.tools.phi_source_theorem_linkage_obligation_packet_result_review_report import (
    NEXT_TARGET as PHI_SOURCE_ATTEMPT_TARGET,
    OUTCOME_ID as PHI_SOURCE_PACKET_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as STRICT_PHI_SOURCE_PACKET_REVIEW_OUTCOME,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_report import (
    NEXT_TARGET as PHI_SOURCE_ATTEMPT_REVIEW_TARGET,
    OUTCOME_ID as PHI_SOURCE_ATTEMPT_OUTCOME,
    STRICT_ATTEMPT_PREPARATION_RESULT as STRICT_PHI_SOURCE_ATTEMPT_OUTCOME,
)
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review_report import (
    NEXT_TARGET as PHI_SOURCE_ATTEMPT_EXECUTION_TARGET,
    OUTCOME_ID as PHI_SOURCE_ATTEMPT_REVIEW_OUTCOME,
    STRICT_REVIEW_RESULT as STRICT_PHI_SOURCE_ATTEMPT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "A_source_theorem_linkage_attempt_from_standalone_A_route_result_review_report.py"
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

    if active["workstream_id"] == PHI_SOURCE_PACKET_REVIEW_TARGET:
        assert active["status"] == "active"
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
        return

    phi_packet_review = _workstream(registry, PHI_SOURCE_PACKET_REVIEW_TARGET)
    assert phi_packet_review["status"] == "paused"
    assert phi_packet_review["review_result"] == PHI_SOURCE_PACKET_REVIEW_OUTCOME
    assert phi_packet_review["strict_review_result"] == (
        STRICT_PHI_SOURCE_PACKET_REVIEW_OUTCOME
    )
    assert phi_packet_review["selected_next_target"] == PHI_SOURCE_ATTEMPT_TARGET
    assert phi_packet_review["C_source_phi_discharged"] == "no"
    assert phi_packet_review["A_source_route_imported"] == "no"
    assert phi_packet_review["psi_A_sourced_Maxwell_imported"] == "no"
    assert phi_packet_review["QFT_GR_source_route_imported"] == "no"
    assert phi_packet_review["rule_promoted"] == "no"
    assert phi_packet_review["master_action_promoted"] == "no"

    if active["workstream_id"] == PHI_SOURCE_ATTEMPT_TARGET:
        assert active["status"] == "active"
        assert active["consumed_target"] == PHI_SOURCE_PACKET_REVIEW_TARGET
        assert active["review_result"] == PHI_SOURCE_PACKET_REVIEW_OUTCOME
        assert active["strict_review_result"] == STRICT_PHI_SOURCE_PACKET_REVIEW_OUTCOME
        assert active["attempt_preparation_result"] == "PENDING"
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

    phi_attempt = _workstream(registry, PHI_SOURCE_ATTEMPT_TARGET)
    assert phi_attempt["status"] == "paused"
    assert phi_attempt["attempt_preparation_result"] == PHI_SOURCE_ATTEMPT_OUTCOME
    assert phi_attempt["strict_attempt_preparation_result"] == (
        STRICT_PHI_SOURCE_ATTEMPT_OUTCOME
    )
    assert phi_attempt["selected_next_target"] == PHI_SOURCE_ATTEMPT_REVIEW_TARGET
    assert phi_attempt["proof_attempt_executed"] == "no"
    assert phi_attempt["theorem_discharged"] == "no"
    assert phi_attempt["C_source_phi_discharged"] == "no"
    assert phi_attempt["A_source_route_imported"] == "no"
    assert phi_attempt["psi_A_sourced_Maxwell_imported"] == "no"
    assert phi_attempt["QFT_GR_source_route_imported"] == "no"
    assert phi_attempt["rule_promoted"] == "no"
    assert phi_attempt["master_action_promoted"] == "no"

    if active["workstream_id"] == PHI_SOURCE_ATTEMPT_REVIEW_TARGET:
        assert active["status"] == "active"
        assert active["consumed_target"] == PHI_SOURCE_ATTEMPT_TARGET
        assert active["attempt_preparation_result"] == PHI_SOURCE_ATTEMPT_OUTCOME
        assert active["strict_attempt_preparation_result"] == (
            STRICT_PHI_SOURCE_ATTEMPT_OUTCOME
        )
        assert active["review_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["proof_attempt_executed"] == "no"
        assert active["theorem_discharged"] == "no"
        assert active["C_source_phi_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"
        return

    phi_attempt_review = _workstream(registry, PHI_SOURCE_ATTEMPT_REVIEW_TARGET)
    assert phi_attempt_review["status"] == "paused"
    assert phi_attempt_review["review_result"] == PHI_SOURCE_ATTEMPT_REVIEW_OUTCOME
    assert phi_attempt_review["strict_review_result"] == (
        STRICT_PHI_SOURCE_ATTEMPT_REVIEW_OUTCOME
    )
    assert phi_attempt_review["selected_next_target"] == (
        PHI_SOURCE_ATTEMPT_EXECUTION_TARGET
    )
    assert phi_attempt_review["proof_attempt_executed"] == "no"
    assert phi_attempt_review["theorem_discharged"] == "no"
    assert phi_attempt_review["C_source_phi_discharged"] == "no"
    assert phi_attempt_review["A_source_route_imported"] == "no"
    assert phi_attempt_review["psi_A_sourced_Maxwell_imported"] == "no"
    assert phi_attempt_review["QFT_GR_source_route_imported"] == "no"
    assert phi_attempt_review["rule_promoted"] == "no"
    assert phi_attempt_review["master_action_promoted"] == "no"

    assert active["status"] == "active"
    assert active["workstream_id"] == PHI_SOURCE_ATTEMPT_EXECUTION_TARGET
    assert active["consumed_target"] == PHI_SOURCE_ATTEMPT_REVIEW_TARGET
    assert active["review_result"] == PHI_SOURCE_ATTEMPT_REVIEW_OUTCOME
    assert active["strict_review_result"] == STRICT_PHI_SOURCE_ATTEMPT_REVIEW_OUTCOME
    assert active["execution_result"] == "PENDING"
    assert active["selected_next_target"] == "PENDING"
    assert active["proof_attempt_executed"] == "no"
    assert active["C_source_phi_discharged"] == "no"
    assert active["phi_sector_closure_claimed"] == "no"
    assert active["A_source_route_imported"] == "no"
    assert active["psi_A_sourced_Maxwell_imported"] == "no"
    assert active["QFT_GR_source_route_imported"] == "no"
    assert active["rule_promoted"] == "no"
    assert active["master_action_promoted"] == "no"


def consumed_target() -> str:
    return "review_A_source_theorem_linkage_attempt_from_standalone_A_route_result"


def preparation_target() -> str:
    return "prepare_A_source_theorem_linkage_attempt_from_standalone_A_route"


def test_A_source_standalone_attempt_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_A_source_standalone_attempt_result_review_accepts_preparation() -> None:
    review = _json(DEFAULT_OUT)

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["reviewed"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == OUTCOME_ID
    assert review["packet_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == consumed_target()
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["suggested_execution_outcome"] == SUGGESTED_EXECUTION_OUTCOME
    assert review["strict_suggested_execution_outcome"] == (
        STRICT_SUGGESTED_EXECUTION_OUTCOME
    )
    assert review["attempt_preparation_result"] == ATTEMPT_OUTCOME
    assert review["attempt_strict_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert (
        build_A_source_theorem_linkage_attempt_from_standalone_A_route_result_review()
        == review
    )


def test_A_source_standalone_attempt_result_review_preserves_route() -> None:
    review = _json(DEFAULT_OUT)

    assert review["standalone_A_sector_route"] == STANDALONE_A_ROUTE
    assert review["standalone_A_sector_route_preserved"] is True
    assert review["standalone_A_stress_conservation_route"] == (
        SOURCE_ADMISSIBILITY_CONDITION
    )
    assert review["source_admissibility_condition"] == "nabla_mu T_A^{mu nu} = 0"
    assert review["C_source_A_residual_definition"] == (
        C_SOURCE_A_RESIDUAL_DEFINITION
    )
    assert review["target_conclusion"] == TARGET_CONCLUSION
    assert review["execution_route_to_authorize"] == EXECUTION_ROUTE_TO_AUTHORIZE
    assert review["linkage_route"] == LINKAGE_ROUTE
    assert review["watch_items"] == WATCH_ITEMS
    assert review["route_kind"] == "standalone_A_stress_conservation"
    assert review["source_free_standalone_boundary_preserved"] is True


def test_A_source_standalone_attempt_result_review_blocks_J_and_psi_A_route() -> None:
    review = _json(DEFAULT_OUT)
    route_text = " ".join(review["execution_route_to_authorize"])

    assert review["J_current_imported"] is False
    assert review["psi_A_sourced_maxwell_route"] == PSI_A_SOURCED_MAXWELL_ROUTE
    assert review["psi_A_sourced_route_substituted"] is False
    assert review["sourced_Maxwell_route_substituted"] is False
    assert review["do_not_silently_substitute_psi_A_sourced_Maxwell_route"] is True
    assert review["route_contamination_guard"] == PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD
    assert "J^alpha" not in route_text
    assert "J current" not in route_text
    assert "nabla_mu F^{mu alpha} = J^alpha" not in route_text


def test_A_source_standalone_attempt_result_review_preserves_boundaries() -> None:
    review = _json(DEFAULT_OUT)

    for flag in [
        "review_executes_theorem",
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_execution_authorized",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_source_A_closure_claimed",
        "C_source_A_discharged",
        "A_source_theorem_linkage_obligation_discharged",
        "J_current_imported",
        "psi_A_sourced_route_substituted",
        "sourced_Maxwell_route_substituted",
        "gap_1_through_gap_8_discharged",
        "general_C_k_closure",
        "C_k_dynamical_law_status",
        "C_k_rule_promoted",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "action_embedding_claimed",
        "action_variation_executed",
        "A_sector_closure_claimed",
        "sourced_maxwell_closure_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[flag] is False, flag

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_REVIEW
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert review["scoped_lean_targets_status_for_review"] == "PASSED_SERIAL_RERUN"
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_A_source_standalone_attempt_result_review_rotates_to_execution() -> None:
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

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    if consumed_target() not in registry["paused_lanes"]:
        assert active_workstream(registry)["workstream_id"] == consumed_target()
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    attempt = _workstream(registry, preparation_target())
    assert attempt["status"] == "paused"
    assert attempt["authorization_evidence"] == _rel(ATTEMPT_LEAN_PACKET_PATH)
    assert attempt["report"] == _rel(ATTEMPT_OUT)
    assert attempt["attempt_preparation_result"] == ATTEMPT_OUTCOME
    assert attempt["strict_attempt_preparation_result"] == (
        STRICT_ATTEMPT_PREPARATION_RESULT
    )
    assert attempt["selected_next_target"] == consumed_target()

    consumed = _workstream(registry, consumed_target())
    if consumed["status"] == "active":
        assert consumed["prior_result_review_outcome"] == OUTCOME_ID
        assert consumed["prior_strict_result_review_outcome"] == STRICT_REVIEW_RESULT
        assert consumed["execution_result"] == SUGGESTED_EXECUTION_OUTCOME
        assert consumed["strict_execution_result"] == STRICT_SUGGESTED_EXECUTION_OUTCOME
        assert consumed["review_result"] == "PENDING"
        assert consumed["selected_next_target"] == "PENDING"
        assert consumed["C_source_A_zero_derived"] == "yes"
        assert consumed["J_current_imported"] == "no"
        assert consumed["psi_A_sourced_route_substituted"] == "no"
        assert consumed["rule_promoted"] == "no"
        assert consumed["master_action_promoted"] == "no"
    else:
        assert consumed["status"] == "paused"
        assert consumed["attempt_preparation_result"] == ATTEMPT_OUTCOME
        if consumed["review_result"] == OUTCOME_ID:
            assert consumed["authorization_evidence"] == evidence
            assert consumed["report"] == report
            assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
            assert consumed["selected_next_target"] == NEXT_TARGET
            assert consumed["theorem_discharged"] == "no"
            assert consumed["C_source_A_discharged"] == "no"
        else:
            assert consumed["authorization_evidence"] == _rel(
                EXECUTION_REVIEW_LEAN_PACKET_PATH
            )
            assert consumed["report"] == _rel(EXECUTION_REVIEW_OUT)
            assert consumed["review_result"] == EXECUTION_REVIEW_OUTCOME
            assert consumed["strict_review_result"] == EXECUTION_REVIEW_STRICT_OUTCOME
            assert consumed["execution_result"] == SUGGESTED_EXECUTION_OUTCOME
            assert consumed["strict_execution_result"] == (
                STRICT_SUGGESTED_EXECUTION_OUTCOME
            )
            assert consumed["selected_next_target"] == CLOSEOUT_TARGET
            assert consumed["theorem_discharged"] == "yes"
            assert consumed["C_source_A_discharged"] == "yes"
            assert consumed["C_source_A_zero_derived"] == "yes"
        assert consumed["C_source_A_residual_definition"] == C_SOURCE_A_RESIDUAL_DEFINITION
        assert consumed["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
        assert consumed["target_conclusion"] == TARGET_CONCLUSION
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
        assert active["execution_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["C_source_A_residual_definition"] == C_SOURCE_A_RESIDUAL_DEFINITION
        assert active["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
        assert active["target_conclusion"] == TARGET_CONCLUSION
        assert active["J_current_imported"] == "no"
        assert active["psi_A_sourced_route_substituted"] == "no"
        assert active["C_source_A_discharged"] == "no"
        assert active["sourced_maxwell_closure_claimed"] == "no"
        assert active["full_maxwell_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        executed = _workstream(
            registry,
            "execute_A_source_theorem_linkage_attempt_from_standalone_A_route",
        )
        assert executed["status"] == "paused"
        assert executed["execution_result"] == SUGGESTED_EXECUTION_OUTCOME
        assert executed["strict_execution_result"] == STRICT_SUGGESTED_EXECUTION_OUTCOME
        assert executed["selected_next_target"] == consumed_target()
        assert executed["proof_attempt_executed"] == "yes"
        assert executed["theorem_discharged"] == "yes"
        assert executed["C_source_A_zero_derived"] == "yes"
        assert executed["J_current_imported"] == "no"
        assert executed["psi_A_sourced_route_substituted"] == "no"
        assert executed["rule_promoted"] == "no"
        assert executed["master_action_promoted"] == "no"

        if active["workstream_id"] == consumed_target():
            assert active["consumed_target"] == (
                "execute_A_source_theorem_linkage_attempt_from_standalone_A_route"
            )
            assert active["execution_result"] == SUGGESTED_EXECUTION_OUTCOME
            assert active["review_result"] == "PENDING"
            assert active["selected_next_target"] == "PENDING"
        else:
            reviewed = _workstream(registry, consumed_target())
            assert reviewed["status"] == "paused"
            assert reviewed["review_result"] == EXECUTION_REVIEW_OUTCOME
            assert reviewed["strict_review_result"] == EXECUTION_REVIEW_STRICT_OUTCOME
            assert reviewed["selected_next_target"] == CLOSEOUT_TARGET

            if active["workstream_id"] == CLOSEOUT_TARGET:
                assert active["status"] == "active"
                assert active["consumed_target"] == consumed_target()
                assert active["closeout_outcome_suggested"] == CLOSEOUT_OUTCOME
                assert active["closeout_result"] == "PENDING"
            else:
                closeout = _workstream(registry, CLOSEOUT_TARGET)
                assert closeout["status"] == "paused"
                assert closeout["closeout_result"] == CLOSEOUT_RESULT
                assert closeout["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
                assert closeout["selected_next_target"] == CLOSEOUT_REVIEW_TARGET

                if active["workstream_id"] == CLOSEOUT_REVIEW_TARGET:
                    assert active["status"] == "active"
                    assert active["consumed_target"] == CLOSEOUT_TARGET
                    assert active["closeout_result"] == CLOSEOUT_RESULT
                    assert active["review_result"] == "PENDING"
                else:
                    closeout_review = _workstream(registry, CLOSEOUT_REVIEW_TARGET)
                    assert closeout_review["status"] == "paused"
                    assert closeout_review["review_result"] == CLOSEOUT_REVIEW_RESULT
                    assert closeout_review["strict_review_result"] == (
                        STRICT_CLOSEOUT_REVIEW_RESULT
                    )
                    assert closeout_review["selected_next_target"] == (
                        A_SOURCE_SELECTOR_TARGET
                    )

                    _assert_A_source_selector_or_review_active(registry, active)


def test_A_source_standalone_attempt_result_review_mirrors() -> None:
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
        "ASourceTheoremLinkageAttemptFromStandaloneARouteResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SUGGESTED_EXECUTION_OUTCOME,
        STRICT_SUGGESTED_EXECUTION_OUTCOME,
        C_SOURCE_A_RESIDUAL_DEFINITION,
        SOURCE_ADMISSIBILITY_CONDITION,
        TARGET_CONCLUSION,
        PSI_A_SOURCED_MAXWELL_ROUTE,
        PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_OUTCOME_v0",
        "A_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_A_ROUTE_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "no J current imported",
        "no psi-A sourced Maxwell substitution",
        "no theorem discharge during review",
        "no C_source^A closure during review",
        "no A-sector closure",
        "no sourced Maxwell closure",
        "no full Maxwell closure",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_A_source_standalone_attempt_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_A_source_theorem_linkage_attempt_from_standalone_A_route_result_review_gate.py"
    )
