from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_state_admissibility_boundary_assumption_reduction_packet_report import (
    ACCEPTED_PRIOR_ROW_ID,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SELECTED_ASSUMPTION_FAMILY,
    SELECTED_ROW_ID,
    STATE_ADMISSIBILITY_BOUNDARY_CONDITION,
)
from formal.python.tools.qft_gr_state_admissibility_boundary_assumption_reduction_packet_result_review_report import (
    AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_state_admissibility_boundary_assumption_reduction_packet_result_review,
)
from formal.python.tools.qft_gr_state_domain_assumption_reduction_packet_report import (
    PRIOR_COMPLETED_FAMILIES,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StateAdmissibilityBoundaryAssumptionReductionPacketResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_state_admissibility_boundary_assumption_reduction_packet_result_review_report.py"
)
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
V01_INDEX_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
)
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_qft_gr_state_admissibility_boundary_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_state_admissibility_boundary_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert (
        review[
            "consumes_qft_gr_state_admissibility_boundary_assumption_reduction_packet"
        ]
        == PACKET_ID
    )
    assert review["consumed_packet_outcome_id"] == PACKET_OUTCOME
    assert review["consumed_packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == (
        "review_qft_gr_state_admissibility_boundary_assumption_reduction_packet_result"
    )


def test_qft_gr_state_admissibility_boundary_packet_result_review_confirms_row002() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocker"] == "insufficient_assumptions_for_conservation"
    assert review["selected_blocker"] == "insufficient_assumptions_for_conservation"
    assert review["conservation_blocker_remains"] is True
    assert review["completed_prior_assumption_families"] == PRIOR_COMPLETED_FAMILIES
    assert review["completed_prior_assumption_family_count"] == 2
    assert review["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert review["primary_assumption_reduction_family"] == SELECTED_ASSUMPTION_FAMILY
    assert review["accepted_prior_state_domain_assumption_row"] == ACCEPTED_PRIOR_ROW_ID
    assert review["accepted_state_domain_assumption_rows"] == [ACCEPTED_PRIOR_ROW_ID]
    assert review["selected_state_domain_assumption_row"] == SELECTED_ROW_ID
    assert review["selected_row_count"] == 1
    assert review["state_admissibility_boundary_status_tokens"] == [
        "required",
        "missing",
        "candidate_reducible",
    ]
    assert review["state_admissibility_boundary_condition"] == (
        STATE_ADMISSIBILITY_BOUNDARY_CONDITION
    )
    assert review["packet_preparation_only_confirmed"] is True


def test_qft_gr_state_admissibility_boundary_packet_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["state_admissibility_boundary_assumption_reduced_by_review"] is False
    assert (
        review[
            "state_admissibility_boundary_assumption_reduced_or_discharged_by_review"
        ]
        is False
    )
    assert review["state_admissibility_claimed"] is False
    assert review["state_admissibility_discharged"] is False
    assert review["state_admissibility_boundary_satisfied"] is False
    assert review["state_admissibility_boundary_discharged"] is False
    assert review["state_domain_assumptions_discharged_by_review"] is False
    assert review["state_domain_assumptions_reduced_or_discharged_by_review"] is False
    assert review["proof_object_constructed"] is False
    assert review["conservation_proof_object_constructed"] is False
    assert review["conservation_witness_constructed"] is False
    assert review["source_admissibility_claimed"] is False
    assert review["stress_energy_source_admissibility_claimed"] is False
    assert review["Bianchi_compatibility_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False
    assert review["master_action_promotion_authorized"] is False
    assert review["release_assembly_authorized"] is False
    assert review["public_submission_authorized"] is False


def test_qft_gr_state_admissibility_boundary_packet_result_review_selects_one_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selection_count"] == 1
    assert review["selected_next_target_count"] == 1
    assert review["bounded_reduction_attempt_authorized"] is True
    assert review["bounded_reduction_attempt_executed"] is False
    assert review["authorized_attempt_result_classifications"] == (
        AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS
    )
    target_decisions = {
        row["target"]: row["decision"] for row in review["candidate_next_targets"]
    }
    assert target_decisions[NEXT_TARGET] == "selected"
    assert (
        target_decisions[
            "prepare_qft_gr_state_expectation_compatibility_assumption_reduction_packet"
        ]
        == "deferred"
    )
    assert target_decisions["claim_qft_gr_state_admissibility"] == "not_authorized"
    assert target_decisions["claim_qft_gr_source_admissibility"] == "not_authorized"
    assert target_decisions["construct_qft_gr_conservation_proof_object"] == (
        "not_authorized"
    )
    assert target_decisions["construct_qft_gr_conservation_witness"] == (
        "not_authorized"
    )
    assert target_decisions["claim_qft_gr_bianchi_compatibility"] == (
        "not_authorized"
    )
    assert target_decisions["derive_semiclassical_einstein_equation"] == (
        "not_authorized"
    )
    assert target_decisions["close_qft_gr_seam"] == "not_authorized"


def test_qft_gr_state_admissibility_boundary_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = (
        build_qft_gr_state_admissibility_boundary_assumption_reduction_packet_result_review(
            packet_path=PACKET_PATH,
            captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
        )
    )
    assert review == generated
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            SURFACES_PATH,
            REGISTRY_PATH,
            ROADMAP_PATH,
            LEAN_REVIEW_PATH,
            V01_INDEX_PATH,
            FRONTIER_PATH,
        ]
    )
    for token in [
        REVIEW_ID,
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        ACCEPTED_PRIOR_ROW_ID,
        SELECTED_ROW_ID,
        STATE_ADMISSIBILITY_BOUNDARY_CONDITION,
        NEXT_TARGET,
    ]:
        assert token in joined
