from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_state_domain_assumption_reduction_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_state_domain_assumption_reduction_packet_result_review_report import (
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    SELECTED_BOUNDED_STATE_DOMAIN_ROW,
    build_qft_gr_state_domain_assumption_reduction_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StateDomainAssumptionReductionPacketResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_state_domain_assumption_reduction_packet_result_review_report.py"
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


def test_qft_gr_state_domain_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_state_domain_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumes_qft_gr_state_domain_assumption_reduction_packet"] == (
        PACKET_ID
    )
    assert review["consumed_packet_outcome_id"] == PACKET_OUTCOME
    assert review["consumed_packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == (
        "review_qft_gr_state_domain_assumption_reduction_packet_result"
    )


def test_qft_gr_state_domain_packet_result_review_accepts_preparation_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["blocker"] == "insufficient_assumptions_for_conservation"
    assert review["selected_blocker"] == "insufficient_assumptions_for_conservation"
    assert review["conservation_blocker_remains"] is True
    assert review["completed_prior_assumption_families"] == [
        "operator_domain_assumptions",
        "renormalization_assumptions",
    ]
    assert review["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert review["primary_assumption_reduction_family"] == SELECTED_ASSUMPTION_FAMILY
    assert review["state_domain_family_analysis_accepted"] is True
    assert review["state_domain_assumption_reduction_packet_reviewed"] is True
    assert review["state_domain_assumption_reduction_packet_accepted"] is True
    assert review["packet_preparation_only_confirmed"] is True
    assert review["state_domain_assumptions_discharged_by_review"] is False
    assert review["state_domain_assumptions_reduced_by_review"] is False
    assert review["state_domain_assumptions_reduced_or_discharged_by_review"] is False
    assert review["bounded_state_domain_reduction_attempt_authorized_by_review"] is False


def test_qft_gr_state_domain_packet_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["conservation_proved"] is False
    assert review["actual_conservation_claimed"] is False
    assert review["covariant_conservation_statement_proved"] is False
    assert review["proof_object_constructed"] is False
    assert review["conservation_proof_object_constructed"] is False
    assert review["conservation_witness_constructed"] is False
    assert review["source_admissibility_claimed"] is False
    assert review["stress_energy_source_admissibility_claimed"] is False
    assert review["Bianchi_compatibility_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["scientific_validation_claimed"] is False
    assert review["master_action_promoted"] is False
    assert review["master_action_promotion_authorized"] is False
    assert review["release_assembly_authorized"] is False
    assert review["release_packet_assembled"] is False
    assert review["public_submission_authorized"] is False


def test_qft_gr_state_domain_packet_result_review_selects_first_packet_row() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert packet["candidate_reducible_assumptions"][0]["assumption_id"] == (
        SELECTED_BOUNDED_STATE_DOMAIN_ROW
    )
    assert review["selected_bounded_state_domain_assumption_row"] == (
        SELECTED_BOUNDED_STATE_DOMAIN_ROW
    )
    assert review["selected_bounded_state_domain_assumption_target"] == NEXT_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selection_count"] == 1
    assert review["selected_next_target_count"] == 1
    target_decisions = {
        row["target"]: row["decision"] for row in review["candidate_next_targets"]
    }
    assert target_decisions[NEXT_TARGET] == "selected"
    assert (
        target_decisions[
            "prepare_qft_gr_state_admissibility_boundary_assumption_reduction_packet"
        ]
        == "deferred"
    )
    assert (
        target_decisions[
            "prepare_qft_gr_state_expectation_compatibility_assumption_reduction_packet"
        ]
        == "deferred"
    )
    assert target_decisions["execute_qft_gr_state_domain_assumption_reduction_attempt"] == (
        "not_authorized"
    )
    assert target_decisions["construct_qft_gr_conservation_proof_object"] == (
        "not_authorized"
    )
    assert target_decisions["construct_qft_gr_conservation_witness"] == (
        "not_authorized"
    )
    assert target_decisions["close_qft_gr_seam"] == "not_authorized"


def test_qft_gr_state_domain_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_state_domain_assumption_reduction_packet_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
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
        SELECTED_BOUNDED_STATE_DOMAIN_ROW,
        NEXT_TARGET,
    ]:
        assert token in joined
