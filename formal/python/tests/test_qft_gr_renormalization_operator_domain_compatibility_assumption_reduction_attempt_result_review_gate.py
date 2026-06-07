from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_renormalization_assumption_reduction_packet_report import (
    BLOCKER,
    OPERATOR_DOMAIN_COMPATIBILITY,
    RENORMALIZED_EXPECTATION_DOMAIN,
    RENORMALIZED_STRESS_ENERGY_OBJECT,
    SELECTED_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_report import (
    BOUNDED_OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_STATUS,
    DEFAULT_OUT as ATTEMPT_PATH,
    OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_ID,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as ATTEMPT_CLASSIFICATION,
)
from formal.python.tools.qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review,
)
from formal.python.tools.qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet_report import (
    ACCEPTED_PRIOR_ROWS,
    CANDIDATE_REDUCTION_ROUTE,
    OPERATOR_DOMAIN_COMPATIBILITY_BOUNDARIES,
    OPERATOR_DOMAIN_COMPATIBILITY_STATUS,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SELECTED_ROW_ID,
)
from formal.python.tools.qft_gr_renormalization_assumption_reduction_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as RENORMALIZATION_PACKET_PATH,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_RenormalizationOperatorDomainCompatibilityAssumptionReductionAttemptResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "qft_gr_renormalization_operator_domain_compatibility_assumption_"
        "reduction_attempt_result_review_report.py"
    )
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


def test_qft_gr_renormalization_operator_domain_compatibility_attempt_result_review_files_exist() -> None:
    assert ATTEMPT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_renormalization_operator_domain_compatibility_attempt_result_review_consumes_attempt() -> None:
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
    assert review["consumed_attempt_result_classification"] == ATTEMPT_CLASSIFICATION
    assert (
        attempt["selected_next_target"]
        == "review_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result"
    )


def test_qft_gr_renormalization_operator_domain_compatibility_attempt_result_review_accepts_row005_only() -> None:
    review = _json(DEFAULT_OUT)
    contract = review["operator_domain_compatibility_reduction_contract"]
    assert review["blocker"] == BLOCKER
    assert review["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert review["accepted_prior_renormalization_assumption_rows"] == ACCEPTED_PRIOR_ROWS
    assert review["selected_renormalization_assumption_row"] == SELECTED_ROW_ID
    assert review["accepted_renormalization_assumption_row"] == SELECTED_ROW_ID
    assert review["accepted_renormalization_assumption_rows"] == [
        *ACCEPTED_PRIOR_ROWS,
        SELECTED_ROW_ID,
    ]
    assert review["accepted_contract_id"] == OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_ID
    assert (
        review["bounded_operator_domain_compatibility_contract_status"]
        == BOUNDED_OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_STATUS
    )
    assert contract["contract_id"] == OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_ID
    assert contract["assumption_id"] == SELECTED_ROW_ID
    assert contract["candidate_stress_energy_object"] == RENORMALIZED_STRESS_ENERGY_OBJECT
    assert contract["renormalized_expectation_domain"] == RENORMALIZED_EXPECTATION_DOMAIN
    assert contract["operator_domain_compatibility"] == OPERATOR_DOMAIN_COMPATIBILITY
    assert contract["scope_boundaries"] == OPERATOR_DOMAIN_COMPATIBILITY_BOUNDARIES
    assert review["operator_domain_compatibility_status"] == (
        OPERATOR_DOMAIN_COMPATIBILITY_STATUS
    )
    assert review["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert review["candidate_reduction_route"] == CANDIDATE_REDUCTION_ROUTE
    assert (
        review[
            "operator_domain_compatibility_assumption_reduction_attempt_result_reviewed"
        ]
        is True
    )
    assert review["operator_domain_compatibility_assumption_reduction_accepted"] is True
    assert review["operator_domain_compatibility_assumption_reduction_rejected"] is False


def test_qft_gr_renormalization_operator_domain_compatibility_attempt_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert (
        review[
            "operator_domain_compatibility_assumption_reduced_pending_result_review_accepted"
        ]
        is True
    )
    assert review["operator_domain_compatibility_assumption_discharged"] is False
    assert review["operator_domain_compatibility_assumption_discharged_by_review"] is False
    assert review["operator_domain_compatibility_discharged"] is False
    assert review["operator_domain_compatibility_discharged_by_implication"] is False
    assert review["operator_domain_compatibility_reduced_or_discharged_by_review"] is False
    assert (
        review["operator_domain_compatibility_reduced_or_discharged_by_implication"]
        is False
    )
    assert review["operator_domain_compatibility_claimed_as_source_admissibility"] is False
    assert review["operator_domain_compatibility_claimed_as_bianchi_compatibility"] is False
    assert review["conservation_proof_object_constructed"] is False
    assert review["conservation_witness_constructed"] is False
    assert review["source_admissibility_claimed"] is False
    assert review["Bianchi_compatibility_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False
    assert review["master_action_promotion_authorized"] is False
    assert review["release_assembly_authorized"] is False
    assert review["release_packet_assembled"] is False
    assert review["public_submission_authorized"] is False
    assert review["publication_authorized"] is False


def test_qft_gr_renormalization_operator_domain_compatibility_attempt_result_review_selects_closeout_packet() -> None:
    review = _json(DEFAULT_OUT)
    assert review["repo_authoritative_renormalization_row_inventory"] == [
        *ACCEPTED_PRIOR_ROWS,
        SELECTED_ROW_ID,
    ]
    assert review["repo_authoritative_renormalization_row_inventory_exhausted"] is True
    assert review["no_next_renormalization_assumption_row_available"] is True
    assert review["next_renormalization_assumption_row"] is None
    assert review["renormalization_assumption_reduction_closeout_packet_authorized"] is True
    assert review["renormalization_assumption_reduction_closeout_preparation_only"] is True
    assert review["renormalization_assumption_reduction_closeout_target"] == NEXT_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "select_next_renormalization_assumption_row": "not_authorized",
        "discharge_qft_gr_renormalization_operator_domain_compatibility_assumption": "not_authorized",
        "construct_qft_gr_conservation_proof_object": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_release_assembly_or_public_submission": "not_authorized",
    }


def test_qft_gr_renormalization_operator_domain_compatibility_attempt_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review(
        attempt_path=ATTEMPT_PATH,
        renormalization_packet_path=RENORMALIZATION_PACKET_PATH,
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
        OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_ID,
        BOUNDED_OPERATOR_DOMAIN_COMPATIBILITY_CONTRACT_STATUS,
        SELECTED_ROW_ID,
        NEXT_TARGET,
    ]:
        assert token in joined
