from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_renormalization_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as RENORMALIZATION_PACKET_PATH,
    OPERATOR_DOMAIN_COMPATIBILITY,
    RENORMALIZED_EXPECTATION_DOMAIN,
    RENORMALIZED_STRESS_ENERGY_OBJECT,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet_report import (
    ACCEPTED_PRIOR_ROWS,
    CANDIDATE_REDUCTION_ROUTE,
    DEFAULT_OUT,
    FAILURE_MODE_IF_UNRESOLVED,
    NEXT_TARGET,
    OPERATOR_DOMAIN_COMPATIBILITY_BOUNDARIES,
    OPERATOR_DOMAIN_COMPATIBILITY_STATUS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SCHEMA_ID,
    SELECTED_ROW_ID,
    build_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet,
)
from formal.python.tools.qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT as ATTEMPT_RESULT_REVIEW_PATH,
    OUTCOME_ID as ATTEMPT_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as ATTEMPT_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as ATTEMPT_RESULT_REVIEW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_RenormalizationOperatorDomainCompatibilityAssumptionReductionPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet_report.py"
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


def test_qft_gr_renormalization_operator_domain_compatibility_packet_files_exist() -> None:
    assert ATTEMPT_RESULT_REVIEW_PATH.exists()
    assert RENORMALIZATION_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_renormalization_operator_domain_compatibility_packet_consumes_rn004_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(ATTEMPT_RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert (
        packet[
            "consumes_qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt_result_review"
        ]
        == ATTEMPT_RESULT_REVIEW_ID
    )
    assert packet["consumed_result_review_outcome_id"] == ATTEMPT_RESULT_REVIEW_OUTCOME
    assert (
        packet["consumed_result_review_classification"]
        == ATTEMPT_RESULT_REVIEW_CLASSIFICATION
    )
    assert (
        review["selected_next_target"]
        == "prepare_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet"
    )


def test_qft_gr_renormalization_operator_domain_compatibility_packet_selects_only_row005() -> None:
    packet = _json(DEFAULT_OUT)
    selected = packet["renormalization_operator_domain_compatibility_assumption"]
    assert packet["blocker"] == BLOCKER
    assert packet["selected_blocker"] == BLOCKER
    assert packet["conservation_blocker_remains"] is True
    assert packet["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert packet["primary_assumption_reduction_family"] == SELECTED_ASSUMPTION_FAMILY
    assert packet["accepted_prior_renormalization_assumption_rows"] == ACCEPTED_PRIOR_ROWS
    assert packet["accepted_prior_row_count"] == 4
    assert packet["selected_renormalization_assumption_row"] == SELECTED_ROW_ID
    assert packet["selected_row_count"] == 1
    assert selected["assumption_id"] == SELECTED_ROW_ID
    assert selected["assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert selected["current_status"] == ["required", "missing", "candidate_reducible"]
    assert packet["renormalization_operator_domain_compatibility_status_tokens"] == selected[
        "current_status"
    ]


def test_qft_gr_renormalization_operator_domain_compatibility_packet_prepares_requested_fields_only() -> None:
    packet = _json(DEFAULT_OUT)
    selected = packet["renormalization_operator_domain_compatibility_assumption"]
    assert packet["candidate_stress_energy_object"] == RENORMALIZED_STRESS_ENERGY_OBJECT
    assert packet["renormalized_expectation_domain"] == RENORMALIZED_EXPECTATION_DOMAIN
    assert packet["operator_domain_compatibility"] == OPERATOR_DOMAIN_COMPATIBILITY
    assert packet["operator_domain_compatibility_condition"] == (
        OPERATOR_DOMAIN_COMPATIBILITY
    )
    assert selected["operator_domain_compatibility_condition"] == (
        OPERATOR_DOMAIN_COMPATIBILITY
    )
    assert packet["operator_domain_compatibility_status"] == (
        OPERATOR_DOMAIN_COMPATIBILITY_STATUS
    )
    assert selected["operator_domain_compatibility_status"] == (
        OPERATOR_DOMAIN_COMPATIBILITY_STATUS
    )
    assert packet["scope_boundaries"] == OPERATOR_DOMAIN_COMPATIBILITY_BOUNDARIES
    assert selected["scope_boundaries"] == OPERATOR_DOMAIN_COMPATIBILITY_BOUNDARIES
    assert packet["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert selected["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert packet["candidate_reduction_route"] == CANDIDATE_REDUCTION_ROUTE
    assert selected["candidate_reduction_route"] == CANDIDATE_REDUCTION_ROUTE
    assert packet["failure_mode_if_unresolved"] == FAILURE_MODE_IF_UNRESOLVED
    assert selected["failure_mode_if_unresolved"] == FAILURE_MODE_IF_UNRESOLVED
    assert (
        packet[
            "operator_domain_compatibility_assumption_reduction_analysis_prepared"
        ]
        is True
    )
    assert packet["prepares_reduction_analysis_only"] is True


def test_qft_gr_renormalization_operator_domain_compatibility_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["operator_domain_compatibility_discharged"] is False
    assert packet["operator_domain_compatibility_reduced_or_discharged_by_preparation"] is False
    assert packet["renormalization_assumptions_discharged"] is False
    assert packet["assumptions_reduced_or_discharged_by_preparation"] is False
    assert packet["proof_object_constructed"] is False
    assert packet["conservation_proof_object_constructed"] is False
    assert packet["conservation_witness_constructed"] is False
    assert packet["source_admissibility_claimed"] is False
    assert packet["stress_energy_source_admissibility_claimed"] is False
    assert packet["Bianchi_compatibility_claimed"] is False
    assert packet["semiclassical_einstein_equation_derived"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["master_action_promoted"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["public_submission_authorized"] is False


def test_qft_gr_renormalization_operator_domain_compatibility_packet_selects_one_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt": "deferred",
        "discharge_qft_gr_renormalization_operator_domain_compatibility_assumption": "not_authorized",
        "construct_qft_gr_conservation_proof_object": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_release_assembly_or_public_submission": "not_authorized",
    }


def test_qft_gr_renormalization_operator_domain_compatibility_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet(
        attempt_result_review_path=ATTEMPT_RESULT_REVIEW_PATH,
        renormalization_packet_path=RENORMALIZATION_PACKET_PATH,
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
        SELECTED_ROW_ID,
        OPERATOR_DOMAIN_COMPATIBILITY,
        OPERATOR_DOMAIN_COMPATIBILITY_STATUS,
        NEXT_TARGET,
    ]:
        assert token in joined
