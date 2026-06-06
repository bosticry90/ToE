from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conservation_form_scope_assumption_reduction_packet_report import (
    CONSERVATION_FORM_OPTIONS,
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIOR_ACCEPTED_ROW001,
    PRIOR_ACCEPTED_ROW002,
    PRIOR_ACCEPTED_ROW003,
    PRIOR_ACCEPTED_ROW004,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SCHEMA_ID,
    SELECTED_BOUNDED_CONSERVATION_FORM,
    SELECTED_ROW_ID,
    build_qft_gr_conservation_form_scope_assumption_reduction_packet,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    DEFAULT_OUT as OPERATOR_DOMAIN_PACKET_PATH,
    PRIMARY_ASSUMPTION_FAMILY,
    ROW_STATUS_ENUM,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_report import (
    RENORMALIZED_EXPECTATION_DOMAIN_LINK_CONTRACT_ID,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as RESULT_REVIEW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_ConservationFormScopeAssumptionReductionPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_conservation_form_scope_assumption_reduction_packet_report.py"
)
SURFACES_PATH = REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
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


def test_qft_gr_conservation_form_scope_assumption_reduction_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_conservation_form_scope_assumption_reduction_packet_consumes_od004_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert (
        packet[
            "consumes_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_result_review"
        ]
        == RESULT_REVIEW_ID
    )
    assert packet["consumed_result_review_outcome_id"] == RESULT_REVIEW_OUTCOME
    assert packet["consumed_result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["selected_next_target"] == CONSUMED_TARGET
    assert review["completed_operator_domain_row"] == PRIOR_ACCEPTED_ROW004


def test_qft_gr_conservation_form_scope_assumption_reduction_packet_records_prior_rows() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["prior_accepted_operator_domain_assumption_rows"] == [
        PRIOR_ACCEPTED_ROW001,
        PRIOR_ACCEPTED_ROW002,
        PRIOR_ACCEPTED_ROW003,
        PRIOR_ACCEPTED_ROW004,
    ]
    assert (
        packet["prior_accepted_renormalized_expectation_domain_link_contract"]
        == RENORMALIZED_EXPECTATION_DOMAIN_LINK_CONTRACT_ID
    )


def test_qft_gr_conservation_form_scope_assumption_reduction_packet_selects_only_row005() -> None:
    packet = _json(DEFAULT_OUT)
    selected = packet["conservation_form_scope_assumption"]
    assert packet["blocker"] == "insufficient_assumptions_for_conservation"
    assert packet["selected_blocker"] == "insufficient_assumptions_for_conservation"
    assert packet["current_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert packet["selected_assumption_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert packet["primary_assumption_reduction_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert packet["selected_operator_domain_assumption_row"] == SELECTED_ROW_ID
    assert packet["selected_row_count"] == 1
    assert selected["assumption_id"] == SELECTED_ROW_ID
    assert selected["assumption_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert selected["current_status"] == [
        "required",
        "missing",
        "candidate_reducible",
    ]
    assert packet["conservation_form_scope_status_tokens"] == selected["current_status"]
    assert packet["row_status_enum"] == ROW_STATUS_ENUM


def test_qft_gr_conservation_form_scope_assumption_reduction_packet_prepares_requested_fields_only() -> None:
    packet = _json(DEFAULT_OUT)
    selected = packet["conservation_form_scope_assumption"]
    assert packet["conservation_form_options"] == CONSERVATION_FORM_OPTIONS
    assert packet["selected_bounded_conservation_form"] == (
        SELECTED_BOUNDED_CONSERVATION_FORM
    )
    assert packet["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert selected["conservation_form_options"] == CONSERVATION_FORM_OPTIONS
    assert selected["selected_bounded_conservation_form"] == (
        SELECTED_BOUNDED_CONSERVATION_FORM
    )
    assert selected["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert {row["form"]: row["decision"] for row in packet["conservation_form_option_decisions"]} == {
        "weak": "selected",
        "strong": "not_selected",
        "distributional": "not_selected",
    }
    for field in [
        "available_repo_evidence",
        "required_future_proof_object",
        "candidate_reduction_route",
        "claim_ceiling",
        "failure_mode_if_unresolved",
    ]:
        assert selected[field]
    assert packet["conservation_form_scope_assumption_reduction_analysis_prepared"] is True
    assert packet["conservation_form_scope_assumption_discharged"] is False
    assert packet["conservation_form_scope_claimed_as_conservation_proof"] is False


def test_qft_gr_conservation_form_scope_assumption_reduction_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["assumptions_reduced_or_discharged_by_preparation"] is False
    assert packet["conservation_proved"] is False
    assert packet["covariant_conservation_statement_proved"] is False
    assert packet["actual_conservation_claimed"] is False
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


def test_qft_gr_conservation_form_scope_assumption_reduction_packet_selects_one_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_qft_gr_conservation_form_scope_assumption_reduction_attempt": "deferred",
        "prepare_qft_gr_source_admissibility_assumption_reduction_packet": "not_authorized",
        "execute_qft_gr_covariant_conservation_proof_object_attempt": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_conservation_form_scope_assumption_reduction_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_conservation_form_scope_assumption_reduction_packet(
        result_review_path=RESULT_REVIEW_PATH,
        operator_domain_packet_path=OPERATOR_DOMAIN_PACKET_PATH,
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
        SELECTED_BOUNDED_CONSERVATION_FORM,
        REQUIRED_FUTURE_PROOF_OBJECT,
        NEXT_TARGET,
    ]:
        assert token in joined
