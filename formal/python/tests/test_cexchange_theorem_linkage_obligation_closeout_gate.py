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
from formal.python.tools.cexchange_theorem_linkage_obligation_closeout_report import (
    C_EXCHANGE_RESIDUAL_DEFINITION,
    C_EXCHANGE_TARGET_CONCLUSION,
    CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CLOSEOUT_RESULT,
    CLOSEOUT_STATEMENT,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_CLOSEOUT,
    INPUT_ROUTE,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_CLOSEOUT,
    LIKELY_NEXT_OBLIGATION,
    LIKELY_NEXT_SELECTOR_TARGET,
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
    THEOREM_TARGET_ID,
    THEOREM_TARGET_STATEMENT,
    TOP_OBLIGATION_ROW_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_DEFINITION,
    build_cexchange_theorem_linkage_obligation_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "cexchange_theorem_linkage_obligation_closeout_report.py"
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


def test_cexchange_closeout_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_cexchange_closeout_accepts_local_definition_linkage() -> None:
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
    assert (
        closeout["likely_next_selector_target_after_review"]
        == LIKELY_NEXT_SELECTOR_TARGET
    )
    assert closeout["likely_next_obligation_after_closeout"] == LIKELY_NEXT_OBLIGATION
    assert closeout["closeout_statement"] == CLOSEOUT_STATEMENT
    assert build_cexchange_theorem_linkage_obligation_closeout() == closeout


def test_cexchange_closeout_records_claims_and_nonclaims() -> None:
    closeout = _json(DEFAULT_OUT)

    assert closeout["closeout_claims"] == CLOSEOUT_CLAIMS
    assert closeout["nonclaims"] == NONCLAIMS
    assert closeout["claim_boundary"] == CLAIM_BOUNDARY
    assert closeout["input_route"] == INPUT_ROUTE
    assert closeout["proof_style"] == PROOF_STYLE
    assert closeout["theorem_target_id"] == THEOREM_TARGET_ID
    assert closeout["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert closeout["top_obligation_row_id"] == TOP_OBLIGATION_ROW_ID
    assert closeout["total_stress_energy_definition"] == TOTAL_STRESS_ENERGY_DEFINITION
    assert (
        closeout["total_stress_energy_conservation_identity"]
        == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
    )
    assert closeout["C_exchange_residual_definition"] == C_EXCHANGE_RESIDUAL_DEFINITION
    assert closeout["C_exchange_target_conclusion"] == C_EXCHANGE_TARGET_CONCLUSION
    assert closeout["definition_linkage_constructed"] is True
    assert closeout["C_exchange_zero_derived"] is True
    assert closeout["local_cexchange_obligation_closed"] is True
    assert closeout["top_theorem_linkage_obligation_locally_closed"] is True
    assert closeout["closeout_executes_new_proof"] is False
    assert closeout["proof_execution_authorized"] is False

    for key in [
        "general_C_k_theorem_linkage_closure",
        "gap_1_through_gap_8_discharged",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "multiplier_route_selected",
        "penalty_route_selected",
        "direct_dynamical_law_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert closeout[key] is False, key


def test_cexchange_closeout_records_lean_status() -> None:
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


def test_cexchange_closeout_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert not is_current

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == _rel(DEFAULT_OUT)
    assert consumed["closeout_result"] == OUTCOME_ID
    assert consumed["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["local_cexchange_obligation_closed"] == "yes"
    assert consumed["general_C_k_theorem_linkage_closure"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    review = _workstream(registry, NEXT_TARGET)
    assert review["status"] == "paused"
    assert review["closeout_result"] == OUTCOME_ID
    assert (
        review["selected_next_target"]
        == "select_next_ck_family_theorem_linkage_obligation_after_cexchange_closeout"
    )
    assert review["local_cexchange_obligation_closed"] == "yes"
    assert review["general_C_k_theorem_linkage_closure"] == "no"
    assert review["rule_promoted"] == "no"
    assert review["master_action_promoted"] == "no"

    active = active_workstream(registry)
    assert active["status"] == "active"
    assert (
        active["workstream_id"]
        == "select_next_ck_family_theorem_linkage_obligation_after_cexchange_closeout"
    )
    assert active["consumed_target"] == NEXT_TARGET


def test_cexchange_closeout_mirrors() -> None:
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
        "CExchangeTheoremLinkageObligationCloseout",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_NEXT_SELECTOR_TARGET,
        LIKELY_NEXT_OBLIGATION,
        CLOSEOUT_STATEMENT,
        THEOREM_TARGET_STATEMENT,
        TOTAL_STRESS_ENERGY_DEFINITION,
        TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
        C_EXCHANGE_RESIDUAL_DEFINITION,
        C_EXCHANGE_TARGET_CONCLUSION,
        LEAN_STATUS_WORDING_FOR_CLOSEOUT,
        "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_OUTCOME_v0",
        "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_NONCLAIM_BOUNDARY_v0",
        "C_exchange theorem-linkage obligation locally closed",
        "no general C_k theorem-linkage closure",
        "no C_k rule promotion",
        "no action embedding",
        "no variation",
        "no seam closure",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_cexchange_closeout_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_cexchange_theorem_linkage_obligation_closeout_gate.py"
    )
