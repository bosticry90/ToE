from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_report import (
    DEFAULT_OUT as ATTEMPT_PATH,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as ATTEMPT_CLASSIFICATION,
)
from formal.python.tools.qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review,
)
from formal.python.tools.qft_gr_candidate_source_domain_membership_assumption_reduction_packet_report import (
    CANDIDATE_SOURCE_OBJECT,
    OPERATOR_DOMAIN_MEMBERSHIP_CONDITION,
    PRIMARY_ASSUMPTION_FAMILY,
    SELECTED_ROW_ID,
)
from formal.python.tools.qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_report import (
    CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_CONTRACT_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CandidateSourceDomainMembershipAssumptionReductionAttemptResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_report.py"
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


def test_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_files_exist() -> None:
    assert ATTEMPT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_consumes_attempt() -> None:
    review = _json(DEFAULT_OUT)
    attempt = _json(ATTEMPT_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_attempt_outcome_id"] == ATTEMPT_OUTCOME
    assert review["consumed_attempt_classification"] == ATTEMPT_CLASSIFICATION
    assert (
        attempt["selected_next_target"]
        == "review_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result"
    )


def test_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_accepts_contract_only() -> None:
    review = _json(DEFAULT_OUT)
    contract = review["candidate_source_domain_membership_reduction_contract"]
    assert review["selected_assumption_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert review["selected_operator_domain_assumption_row"] == SELECTED_ROW_ID
    assert review["completed_operator_domain_row"] == SELECTED_ROW_ID
    assert review["accepted_contract_id"] == (
        CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_CONTRACT_ID
    )
    assert contract["contract_id"] == CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_CONTRACT_ID
    assert contract["assumption_id"] == SELECTED_ROW_ID
    assert contract["candidate_source_object"] == CANDIDATE_SOURCE_OBJECT
    assert (
        contract["operator_domain_membership_condition"]
        == OPERATOR_DOMAIN_MEMBERSHIP_CONDITION
    )
    assert (
        review[
            "candidate_source_domain_membership_assumption_reduction_attempt_result_reviewed"
        ]
        is True
    )
    assert (
        review["candidate_source_domain_membership_assumption_reduction_accepted"]
        is True
    )
    assert (
        review["candidate_source_domain_membership_assumption_reduction_rejected"]
        is False
    )
    assert review["candidate_source_domain_membership_assumption_discharged"] is False


def test_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["candidate_source_domain_membership_assumption_discharged"] is False
    assert (
        review["candidate_source_domain_membership_assumption_discharged_by_review"]
        is False
    )
    assert review["source_admissibility_claimed"] is False
    assert review["stress_energy_source_admissibility_claimed"] is False
    assert review["assumption_discharge_claimed"] is False
    assert review["assumptions_reduced_or_discharged_by_review"] is False
    assert review["assumptions_reduced_or_discharged_by_implication"] is False
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


def test_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_selects_next_operator_domain_row() -> None:
    review = _json(DEFAULT_OUT)
    assert review["next_operator_domain_assumption_row"] == (
        NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW
    )
    assert review["operator_domain_row_sequence"] == [
        "OD-ASSUMP-001-selected_operator_action",
        "OD-ASSUMP-002-candidate_source_domain_membership",
        NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW,
        "OD-ASSUMP-004-renormalized_expectation_domain_link",
        "OD-ASSUMP-005-conservation_form_scope",
        "OD-ASSUMP-006-metric_connection_scope",
    ]
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_renormalized_expectation_domain_link_assumption_reduction_packet": "deferred",
        "prepare_qft_gr_source_admissibility_assumption_reduction_packet": "not_authorized",
        "execute_qft_gr_covariant_conservation_proof_object_attempt": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_candidate_source_domain_membership_assumption_reduction_attempt_result_review(
        attempt_path=ATTEMPT_PATH,
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
        CANDIDATE_SOURCE_DOMAIN_MEMBERSHIP_CONTRACT_ID,
        NEXT_OPERATOR_DOMAIN_ASSUMPTION_ROW,
        NEXT_TARGET,
    ]:
        assert token in joined
