from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_limit_interchange_regularization_boundary_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_OUT as PACKET_PATH,
    LIMIT_INTERCHANGE_BOUNDARIES,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIOR_COMPLETED_FAMILIES,
    SELECTED_ASSUMPTION_FAMILY,
    SELECTED_ROW_ID,
    SELECTED_ROW_OBJECT,
)
from formal.python.tools.qft_gr_limit_interchange_regularization_boundary_assumption_reduction_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_packet_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_LimitInterchangeRegularizationBoundaryAssumptionReductionPacketResultReview.lean"
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


def test_qft_gr_limit_interchange_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_limit_interchange_packet_result_review_consumes_packet() -> None:
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
            "consumes_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_packet"
        ]
        == PACKET_ID
    )
    assert review["consumed_packet_outcome_id"] == PACKET_OUTCOME
    assert review["consumed_packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == review["consumed_target"]


def test_qft_gr_limit_interchange_packet_result_review_accepts_packet_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["packet_preparation_only_confirmed_by_review"] is True
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_packet_reviewed"
        ]
        is True
    )
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_packet_accepted"
        ]
        is True
    )
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_packet_rejected"
        ]
        is False
    )
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_packet_preparation_only"
        ]
        is True
    )
    assert review["mr_assump_004_attempt_executed_by_review"] is False
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_attempt_authorized"
        ]
        is True
    )
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_attempt_executed"
        ]
        is False
    )


def test_qft_gr_limit_interchange_packet_result_review_preserves_selection() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert review["primary_assumption_reduction_family"] == SELECTED_ASSUMPTION_FAMILY
    assert review["selected_mathematical_regularity_assumption_row"] == SELECTED_ROW_ID
    assert review["selected_bounded_mathematical_regularity_assumption_row"] == (
        SELECTED_ROW_ID
    )
    assert review["selected_row_count"] == 1
    assert review["selected_row_is_repo_authoritative_next_row"] is True
    assert review["limit_interchange_regularization_boundary"] == SELECTED_ROW_OBJECT
    assert review["limit_interchange_boundaries"] == LIMIT_INTERCHANGE_BOUNDARIES
    assert review["completed_prior_assumption_families"] == PRIOR_COMPLETED_FAMILIES
    assert review["operator_domain_assumptions_completed"] is True
    assert review["renormalization_assumptions_completed"] is True
    assert review["state_domain_assumptions_completed"] is True
    assert review["blocker"] == BLOCKER
    assert review["conservation_blocker_remains"] is True


def test_qft_gr_limit_interchange_packet_result_review_selects_attempt_target() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert packet["selected_next_target"] == review["consumed_target"]
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_packet_selected_next_target"
        ]
        == packet["selected_next_target"]
    )
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_packet_result_review_selected_next_target"
        ]
        == NEXT_TARGET
    )
    assert review["packet_result_review_selected_target_split_preserved"] is True
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "review_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_packet_result": "completed_consumed_live_target",
        "discharge_qft_gr_limit_interchange_regularization_boundary_assumption": "not_authorized",
        "discharge_qft_gr_mathematical_regularity_assumptions": "not_authorized",
        "construct_qft_gr_conservation_proof_object": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_state_admissibility": "not_authorized",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_release_assembly_or_public_submission": "not_authorized",
    }


def test_qft_gr_limit_interchange_packet_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["limit_interchange_regularization_boundary_assumption_discharged"] is False
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduced_or_discharged_by_review"
        ]
        is False
    )
    assert review["mathematical_regularity_assumptions_discharged"] is False
    assert review["mathematical_regularity_assumptions_reduced_or_discharged_by_review"] is False
    assert review["assumptions_reduced_or_discharged_by_review"] is False
    assert review["state_admissibility_claimed"] is False
    assert review["state_admissibility_discharged"] is False
    assert review["source_admissibility_claimed"] is False
    assert review["stress_energy_source_admissibility_claimed"] is False
    assert review["conservation_proved"] is False
    assert review["actual_conservation_claimed"] is False
    assert review["proof_object_constructed"] is False
    assert review["conservation_proof_object_constructed"] is False
    assert review["conservation_witness_constructed"] is False
    assert review["Bianchi_compatibility_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False
    assert review["release_assembly_authorized"] is False
    assert review["public_submission_authorized"] is False


def test_qft_gr_limit_interchange_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = (
        build_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_packet_result_review(
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
        SELECTED_ASSUMPTION_FAMILY,
        SELECTED_ROW_ID,
        SELECTED_ROW_OBJECT,
        NEXT_TARGET,
    ]:
        assert token in joined
