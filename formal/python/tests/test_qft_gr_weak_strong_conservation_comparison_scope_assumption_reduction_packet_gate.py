from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT as MR001_RESULT_REVIEW_PATH,
    OUTCOME_ID as MR001_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as MR001_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as MR001_RESULT_REVIEW_ID,
)
from formal.python.tools.qft_gr_mathematical_regularity_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as MATHEMATICAL_REGULARITY_PACKET_PATH,
    PRIOR_COMPLETED_FAMILIES,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_report import (
    ACCEPTED_PRIOR_ROW_ID,
    CANDIDATE_REDUCTION_ROUTE,
    COMPARISON_SCOPE_BOUNDARIES,
    DEFAULT_OUT,
    FAILURE_MODE_IF_UNRESOLVED,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SCHEMA_ID,
    SELECTED_ROW_ID,
    SELECTED_ROW_OBJECT,
    STRONG_CONSERVATION_SCOPE,
    WEAK_CONSERVATION_SCOPE,
    build_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_WeakStrongConservationComparisonScopeAssumptionReductionPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_report.py"
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


def test_qft_gr_weak_strong_conservation_comparison_scope_packet_files_exist() -> None:
    assert MR001_RESULT_REVIEW_PATH.exists()
    assert MATHEMATICAL_REGULARITY_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_weak_strong_conservation_comparison_scope_packet_consumes_mr001_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(MR001_RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert (
        packet[
            "consumes_qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt_result_review"
        ]
        == MR001_RESULT_REVIEW_ID
    )
    assert packet["consumed_result_review_outcome_id"] == MR001_RESULT_REVIEW_OUTCOME
    assert packet["consumed_result_review_classification"] == (
        MR001_RESULT_REVIEW_CLASSIFICATION
    )
    assert review["selected_next_target"] == packet["consumed_target"]


def test_qft_gr_weak_strong_conservation_comparison_scope_packet_selects_only_mr002() -> None:
    packet = _json(DEFAULT_OUT)
    selected = packet["weak_strong_conservation_comparison_scope_assumption"]
    assert packet["blocker"] == BLOCKER
    assert packet["selected_blocker"] == BLOCKER
    assert packet["conservation_blocker_remains"] is True
    assert packet["completed_prior_assumption_families"] == PRIOR_COMPLETED_FAMILIES
    assert packet["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert packet["primary_assumption_reduction_family"] == SELECTED_ASSUMPTION_FAMILY
    assert packet["accepted_prior_mathematical_regularity_assumption_row"] == (
        ACCEPTED_PRIOR_ROW_ID
    )
    assert packet["accepted_mathematical_regularity_assumption_rows"] == [
        ACCEPTED_PRIOR_ROW_ID
    ]
    assert packet["selected_mathematical_regularity_assumption_row"] == SELECTED_ROW_ID
    assert packet["selected_row_count"] == 1
    assert packet["selected_row_is_repo_authoritative_next_row"] is True
    assert selected["assumption_id"] == SELECTED_ROW_ID
    assert selected["assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert selected["current_status"] == [
        "required",
        "missing",
        "candidate_reducible",
    ]
    assert packet["weak_strong_conservation_comparison_scope_status_tokens"] == (
        selected["current_status"]
    )


def test_qft_gr_weak_strong_conservation_comparison_scope_packet_distinguishes_weak_and_strong() -> None:
    packet = _json(DEFAULT_OUT)
    selected = packet["weak_strong_conservation_comparison_scope_assumption"]
    assert packet["weak_strong_conservation_comparison_scope"] == SELECTED_ROW_OBJECT
    assert selected["regularity_condition"] == SELECTED_ROW_OBJECT
    assert packet["weak_conservation_scope"] == WEAK_CONSERVATION_SCOPE
    assert packet["strong_conservation_scope"] == STRONG_CONSERVATION_SCOPE
    assert WEAK_CONSERVATION_SCOPE != STRONG_CONSERVATION_SCOPE
    assert selected["weak_conservation_scope"] == WEAK_CONSERVATION_SCOPE
    assert selected["strong_conservation_scope"] == STRONG_CONSERVATION_SCOPE
    assert packet["comparison_scope_boundaries"] == COMPARISON_SCOPE_BOUNDARIES
    assert selected["comparison_scope_boundaries"] == COMPARISON_SCOPE_BOUNDARIES
    assert packet["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert selected["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert packet["candidate_reduction_route"] == CANDIDATE_REDUCTION_ROUTE
    assert selected["candidate_reduction_route"] == CANDIDATE_REDUCTION_ROUTE
    assert packet["failure_mode_if_unresolved"] == FAILURE_MODE_IF_UNRESOLVED
    assert selected["failure_mode_if_unresolved"] == FAILURE_MODE_IF_UNRESOLVED
    assert bool(packet["available_repo_evidence"])
    assert (
        packet[
            "weak_strong_conservation_comparison_scope_assumption_reduction_analysis_prepared"
        ]
        is True
    )
    assert packet["prepares_reduction_analysis_only"] is True


def test_qft_gr_weak_strong_conservation_comparison_scope_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["weak_conservation_proved"] is False
    assert packet["strong_conservation_proved"] is False
    assert packet["weak_conservation_claimed"] is False
    assert packet["strong_conservation_claimed"] is False
    assert packet["weak_strong_conservation_equivalence_claimed"] is False
    assert packet["weak_strong_conservation_comparison_scope_discharged"] is False
    assert (
        packet[
            "weak_strong_conservation_comparison_scope_reduced_or_discharged_by_preparation"
        ]
        is False
    )
    assert packet["mathematical_regularity_assumptions_discharged"] is False
    assert packet["state_admissibility_claimed"] is False
    assert packet["source_admissibility_claimed"] is False
    assert packet["stress_energy_source_admissibility_claimed"] is False
    assert packet["actual_conservation_claimed"] is False
    assert packet["conservation_proved"] is False
    assert packet["proof_object_constructed"] is False
    assert packet["conservation_proof_object_constructed"] is False
    assert packet["conservation_witness_constructed"] is False
    assert packet["Bianchi_compatibility_claimed"] is False
    assert packet["semiclassical_einstein_equation_derived"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["master_action_promoted"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["public_submission_authorized"] is False


def test_qft_gr_weak_strong_conservation_comparison_scope_packet_selects_one_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt": "deferred",
        "prepare_qft_gr_distributional_pairing_regular_domain_assumption_reduction_packet": "deferred",
        "prove_qft_gr_weak_conservation": "not_authorized",
        "prove_qft_gr_strong_conservation": "not_authorized",
        "construct_qft_gr_conservation_proof_object": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_state_admissibility": "not_authorized",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_release_assembly_or_public_submission": "not_authorized",
    }


def test_qft_gr_weak_strong_conservation_comparison_scope_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet(
        mr001_result_review_path=MR001_RESULT_REVIEW_PATH,
        mathematical_regularity_packet_path=MATHEMATICAL_REGULARITY_PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert packet == generated
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            SURFACES_PATH,
            REGISTRY_PATH,
            ROADMAP_PATH,
            LEAN_PACKET_PATH,
            V01_INDEX_PATH,
            FRONTIER_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        ACCEPTED_PRIOR_ROW_ID,
        SELECTED_ROW_ID,
        SELECTED_ROW_OBJECT,
        WEAK_CONSERVATION_SCOPE,
        STRONG_CONSERVATION_SCOPE,
        NEXT_TARGET,
    ]:
        assert token in joined
