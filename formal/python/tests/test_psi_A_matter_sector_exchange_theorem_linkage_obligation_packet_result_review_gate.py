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
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_report import (
    DEFAULT_OUT as PACKET_OUT,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
)
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result_review_report import (
    ACCEPTED_REVIEW_FINDINGS,
    ADJOINT_DIRAC_EQUATION,
    ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
    BASIS,
    BLOCKED_CLAIMS,
    COMPATIBILITY_ASSUMPTIONS,
    CURRENT_DEFINITION,
    DEFAULT_OUT,
    DIRAC_EQUATION,
    DOMAIN_BOUNDARY_ASSUMPTIONS,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OBLIGATION,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PLAIN_MEANING,
    PROOF_STYLE,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_REVIEW_RESULT,
    TARGET,
    THEOREM_SHAPE_GIVEN,
    THEOREM_SHAPE_THEN,
    THEOREM_TARGET_STATEMENT,
    T_PSI_POLICY,
    WATCH_ITEMS,
    build_psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result_review_report.py"
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


def consumed_target() -> str:
    return "review_psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result"


def packet_target() -> str:
    return "prepare_psi_A_matter_sector_exchange_theorem_linkage_obligation_packet"


def attempt_review_target() -> str:
    return "review_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result"


def test_psi_A_matter_sector_exchange_packet_result_review_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_matter_sector_exchange_packet_result_review_accepts_scope() -> None:
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
    assert review["attempt_preparation_recommended_outcome"] == (
        ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
    )
    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert (
        build_psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result_review()
        == review
    )


def test_psi_A_matter_sector_exchange_packet_result_review_preserves_target_and_watch_items() -> None:
    review = _json(DEFAULT_OUT)

    assert review["theorem_shape"] == {
        "given": THEOREM_SHAPE_GIVEN,
        "then": THEOREM_SHAPE_THEN,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
    }
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["T_psi_policy"] == T_PSI_POLICY
    assert review["dirac_equation"] == DIRAC_EQUATION
    assert review["adjoint_dirac_equation"] == ADJOINT_DIRAC_EQUATION
    assert review["current_definition"] == CURRENT_DEFINITION
    assert review["compatibility_assumptions"] == COMPATIBILITY_ASSUMPTIONS
    assert review["domain_boundary_assumptions"] == DOMAIN_BOUNDARY_ASSUMPTIONS
    assert review["watch_items"] == WATCH_ITEMS
    assert review["watch_item_count"] == 10
    assert review["blocked_claims"] == BLOCKED_CLAIMS
    assert review["review_executes_proof"] is False
    assert review["proof_execution_authorized"] is False
    assert review["proof_attempt_executed"] is False
    assert review["theorem_discharged"] is False
    assert review["theorem_linkage_obligation_discharged"] is False
    assert review["gap_1_through_gap_8_discharged"] is False
    assert review["rule_promoted"] is False
    assert review["C_k_action_embedding_claimed"] is False
    assert review["C_k_action_variation_executed"] is False
    assert review["full_maxwell_closure_claimed"] is False
    assert review["em_qft_closure_claimed"] is False
    assert review["qft_gr_closure_claimed"] is False
    assert review["gr_qm_closure_claimed"] is False
    assert review["seam_closure_claim"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False


def test_psi_A_matter_sector_exchange_packet_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_PACKET
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
    )
    assert (
        review["scoped_lean_targets_status_for_review"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
    )
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_psi_A_matter_sector_exchange_packet_result_review_rotates_to_attempt_preparation() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)

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
    assert consumed_target() in registry["paused_lanes"]
    if is_current:
        assert NEXT_TARGET not in registry["paused_lanes"]
    else:
        assert NEXT_TARGET in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    packet = workstream(packet_target(), registry)
    assert packet["status"] == "paused"
    assert packet["authorization_evidence"] == _rel(PACKET_LEAN_PACKET_PATH)
    assert packet["report"] == _rel(PACKET_OUT)
    assert packet["packet_result"] == PACKET_OUTCOME

    review_row = workstream(consumed_target(), registry)
    assert review_row["status"] == "paused"
    assert review_row["authorization_evidence"] == evidence
    assert review_row["report"] == _rel(DEFAULT_OUT)
    assert review_row["review_result"] == OUTCOME_ID
    assert review_row["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review_row["selected_next_target"] == NEXT_TARGET
    assert review_row["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review_row["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review_row["watch_items"] == "; ".join(WATCH_ITEMS)
    assert review_row["proof_attempt_executed"] == "no"
    assert review_row["theorem_discharged"] == "no"
    assert review_row["rule_promoted"] == "no"

    handoff = workstream(NEXT_TARGET, registry)
    if is_current:
        assert handoff["status"] == "active"
        assert handoff["active_lane"] == NEXT_TARGET
        assert handoff["authorization_evidence"] == evidence
        assert handoff["report"] == _rel(DEFAULT_OUT)
        assert handoff["consumed_target"] == consumed_target()
        assert handoff["review_result"] == OUTCOME_ID
        assert handoff["strict_review_result"] == STRICT_REVIEW_RESULT
        assert handoff["packet_result"] == "PENDING"
    else:
        assert handoff["status"] == "paused"
    assert handoff["workstream_id"] == NEXT_TARGET
    assert handoff["selected_next_target"] == attempt_review_target()
    assert handoff["selected_next_target_kind"] == (
        "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review"
    )
    assert handoff["selected_obligation"] == OBLIGATION
    assert handoff["basis"] == BASIS
    assert handoff["proof_style"] == PROOF_STYLE
    assert handoff["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert handoff["watch_items"] == "; ".join(WATCH_ITEMS)
    assert handoff["proof_attempt_executed"] == "no"
    assert handoff["theorem_discharged"] == "no"
    assert handoff["rule_promoted"] == "no"
    assert handoff["master_action_promoted"] == "no"


def test_psi_A_matter_sector_exchange_packet_result_review_mirrors() -> None:
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
        "PsiAMatterSectorExchangeTheoremLinkageObligationPacketResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
        THEOREM_TARGET_STATEMENT,
        WATCH_ITEMS[0],
        WATCH_ITEMS[-1],
        LEAN_STATUS_WORDING_FOR_PACKET,
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "same T_psi definition",
        "same F object",
        "same J object",
        "same sign convention",
        "same index placement",
        "same covariant derivative",
        "Dirac equation and adjoint equation",
        "gamma/spin/tetrad compatibility",
        "metric compatibility",
        "shared domain and boundary assumptions",
        "no proof execution during review",
        "no theorem discharge during review",
        "no C_k rule promotion",
        "no C_k action embedding",
        "no C_k variation",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_matter_sector_exchange_packet_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_matter_sector_exchange_theorem_linkage_obligation_packet_result_review_gate.py"
    )
