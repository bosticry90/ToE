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
from formal.python.tools.phi_source_theorem_linkage_obligation_closeout_report import (
    DEFAULT_OUT as CLOSEOUT_PATH,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    OUTCOME_ID as CLOSEOUT_RESULT,
    STRICT_CLOSEOUT_RESULT,
)
from formal.python.tools.phi_source_theorem_linkage_obligation_closeout_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    CLAIM_BOUNDARY,
    CLOSEOUT_CLAIMS,
    CONSUMED_TARGET,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    DEFAULT_OUT,
    EXECUTION_REDUCTION_ROUTE,
    EXECUTION_ROUTE,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
    NEXT_OBLIGATION_REASON,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    NONCLAIMS,
    ON_SHELL_CONDITION,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    RESIDUAL_IDENTITY_FORM,
    REVIEW_RESULT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTOR_QUESTION,
    STRICT_REVIEW_RESULT,
    TARGET_CONCLUSION,
    build_phi_source_theorem_linkage_obligation_closeout_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "phi_source_theorem_linkage_obligation_closeout_result_review_report.py"
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
    rows = [
        row
        for row in payload["workstreams"]
        if row.get("workstream_id") == workstream_id
    ]
    assert rows, f"Missing workstream: {workstream_id}"
    return rows[-1]


def test_phi_source_closeout_result_review_files_exist() -> None:
    for path in [
        CLOSEOUT_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        CLOSEOUT_LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_phi_source_closeout_result_review_accepts_local_closeout() -> None:
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
    assert review["selector_question"] == SELECTOR_QUESTION
    assert review["next_obligation_reason"] == NEXT_OBLIGATION_REASON
    assert (
        build_phi_source_theorem_linkage_obligation_closeout_result_review()
        == review
    )


def test_phi_source_closeout_result_review_preserves_route_and_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["closeout_outcome"] == CLOSEOUT_RESULT
    assert review["closeout_strict_outcome"] == STRICT_CLOSEOUT_RESULT
    assert review["closeout_claims"] == CLOSEOUT_CLAIMS
    assert review["nonclaims"] == NONCLAIMS
    assert review["claim_boundary"] == CLAIM_BOUNDARY
    assert review["C_source_phi_residual_definition"] == (
        C_SOURCE_PHI_RESIDUAL_DEFINITION
    )
    assert review["residual_identity_form"] == RESIDUAL_IDENTITY_FORM
    assert review["on_shell_residual_form"] == ON_SHELL_RESIDUAL_FORM
    assert review["on_shell_condition"] == ON_SHELL_CONDITION
    assert review["target_conclusion"] == TARGET_CONCLUSION
    assert review["execution_route"] == EXECUTION_ROUTE
    assert review["execution_reduction_route"] == EXECUTION_REDUCTION_ROUTE
    assert review["linkage_route"] == EXECUTION_ROUTE
    assert review["plain_meaning"] == PLAIN_MEANING
    assert review["phi_source_theorem_linkage_obligation_closeout_accepted"] is True
    assert review["C_source_phi_definition_preserved"] is True
    assert review["standalone_phi_route_preserved"] is True
    assert review["scalar_on_shell_residual_identity_preserved"] is True
    assert review["scalar_residual_definition_preserved"] is True
    assert review["on_shell_condition_applied"] is True
    assert review["C_source_phi_zero_locally_linked"] is True
    assert review["selector_authorized"] is True
    assert review["selector_executed"] is False
    assert review["next_theorem_linkage_obligation_selected"] is False
    assert review["review_executes_new_proof"] is False
    assert review["proof_execution_authorized"] is False

    for key in [
        "A_source_route_imported",
        "A_sector_route_imported",
        "psi_A_sourced_Maxwell_imported",
        "QFT_GR_source_route_imported",
        "J_current_imported",
        "C_source_phi_closure_claimed",
        "phi_sector_closure_claimed",
        "full_scalar_qft_closure_claimed",
        "full_scalar_QFT_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "general_C_k_closure",
        "general_C_k_theorem_linkage_closure",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "action_embedding_claimed",
        "action_variation_executed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_phi_source_closeout_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_REVIEW
    assert review["lean_status_wording_lines"] == LEAN_STATUS_WORDING_LINES_FOR_REVIEW
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


def test_phi_source_closeout_result_review_rotates_to_selector() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    report = _rel(DEFAULT_OUT)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=CONSUMED_TARGET,
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["consumed_targets"]
    assert CONSUMED_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["closeout_result"] == CLOSEOUT_RESULT
    assert consumed["strict_closeout_result"] == STRICT_CLOSEOUT_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["selector_authorized"] == "yes"
    assert consumed["selector_executed"] == "no"
    assert consumed["next_theorem_linkage_obligation_selected"] == "no"
    assert consumed["C_source_phi_zero_locally_linked"] == "yes"
    assert consumed["phi_sector_closure_claimed"] == "no"
    assert consumed["full_scalar_qft_closure_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["seam_closure_claim"] == "no"
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
        assert active["consumed_target"] == CONSUMED_TARGET
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["selection_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["selector_question"] == SELECTOR_QUESTION
        assert active["selector_authorized"] == "yes"
        assert active["selector_executed"] == "no"
        assert active["proof_attempt_executed"] == "no"
        assert active["theorem_discharged"] == "no"
        assert active["phi_sector_closure_claimed"] == "no"
        assert active["full_scalar_qft_closure_claimed"] == "no"
        assert active["qft_gr_closure_claimed"] == "no"
        assert active["seam_closure_claim"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        assert NEXT_TARGET in registry["completed_targets"]
        assert NEXT_TARGET in registry["consumed_targets"]
        assert NEXT_TARGET in registry["paused_lanes"]


def test_phi_source_closeout_result_review_mirrors() -> None:
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
    route_tokens = EXECUTION_ROUTE if isinstance(EXECUTION_ROUTE, list) else [EXECUTION_ROUTE]
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        STRICT_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "PhiSourceTheoremLinkageObligationCloseoutResultReview",
        CONSUMED_TARGET,
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        SELECTOR_QUESTION,
        C_SOURCE_PHI_RESIDUAL_DEFINITION,
        RESIDUAL_IDENTITY_FORM,
        ON_SHELL_RESIDUAL_FORM,
        ON_SHELL_CONDITION,
        TARGET_CONCLUSION,
        *route_tokens,
        *LEAN_STATUS_WORDING_LINES_FOR_REVIEW,
        "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "phi-source theorem-linkage obligation closeout accepted",
        "standalone phi route preserved",
        "C_source^nu[g, phi] = 0 locally constructed, reviewed, and closed",
        "no phi-sector closure",
        "no full scalar/QFT closure",
        "no QFT-GR closure",
        "no EM-QFT closure",
        "no general C_k closure",
        "no C_k promotion",
        "no action embedding",
        "no variation",
        "no empirical validation",
        "no seam closure",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_phi_source_closeout_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_phi_source_theorem_linkage_obligation_closeout_result_review_gate.py"
    )
