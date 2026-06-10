from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_report import (
    BOUNDED_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_STATUS,
    DEFAULT_OUT as ATTEMPT_PATH,
    LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_ID,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as ATTEMPT_CLASSIFICATION,
)
from formal.python.tools.qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT,
    NEXT_ROW_ID,
    NEXT_ROW_OBJECT,
    NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review,
)
from formal.python.tools.qft_gr_mathematical_regularity_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as PACKET_PATH,
    PRIOR_COMPLETED_FAMILIES,
    SELECTED_ASSUMPTION_FAMILY,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_LimitInterchangeRegularizationBoundaryAssumptionReductionAttemptResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review_report.py"
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


def test_qft_gr_limit_interchange_attempt_result_review_files_exist() -> None:
    assert ATTEMPT_PATH.exists()
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_limit_interchange_attempt_result_review_consumes_attempt() -> None:
    review = _json(DEFAULT_OUT)
    attempt = _json(ATTEMPT_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["review_decision"] == "accept"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_attempt_outcome_id"] == ATTEMPT_OUTCOME
    assert review["consumed_attempt_result_classification"] == ATTEMPT_CLASSIFICATION
    assert (
        attempt["selected_next_target"]
        == "review_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result"
    )


def test_qft_gr_limit_interchange_attempt_result_review_accepts_mr004() -> None:
    review = _json(DEFAULT_OUT)
    contract = review["limit_interchange_regularization_boundary_reduction_contract"]
    assert review["blocker"] == BLOCKER
    assert review["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert review["completed_prior_assumption_families"] == PRIOR_COMPLETED_FAMILIES
    assert review["accepted_mathematical_regularity_assumption_row"] == (
        "MR-ASSUMP-004-limit_interchange_regularization_boundary"
    )
    assert review["accepted_mathematical_regularity_assumption_rows"] == [
        "MR-ASSUMP-004-limit_interchange_regularization_boundary"
    ]
    assert review["accepted_mathematical_regularity_assumption_row_count"] == 1
    assert review["accepted_contract_id"] == LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_ID
    assert (
        review["bounded_limit_interchange_regularization_boundary_contract_status"]
        == BOUNDED_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_STATUS
    )
    assert contract["contract_id"] == LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_ID
    assert contract["assumption_id"] == "MR-ASSUMP-004-limit_interchange_regularization_boundary"
    assert (
        review[
            "limit_interchange_regularization_boundary_assumption_reduction_attempt_result_reviewed"
        ]
        is True
    )
    assert review["limit_interchange_regularization_boundary_assumption_reduction_accepted"] is True
    assert review["limit_interchange_regularization_boundary_assumption_reduction_rejected"] is False


def test_qft_gr_limit_interchange_attempt_result_review_selects_next_row_selection_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["next_mathematical_regularity_assumption_row"] == NEXT_ROW_ID
    assert review["next_mathematical_regularity_assumption_row_object"] == NEXT_ROW_OBJECT
    assert (
        review["next_mathematical_regularity_assumption_row_required_future_proof_object"]
        == NEXT_ROW_REQUIRED_FUTURE_PROOF_OBJECT
    )
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]}[NEXT_TARGET] == "selected"


def test_qft_gr_limit_interchange_attempt_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["limit_interchange_regularization_boundary_assumption_discharged"] is False
    assert review["limit_interchange_regularization_boundary_assumption_discharged_by_review"] is False
    assert review["mathematical_regularity_assumptions_discharged"] is False
    assert review["state_admissibility_claimed"] is False
    assert review["source_admissibility_claimed"] is False
    assert review["conservation_proved"] is False
    assert review["actual_conservation_claimed"] is False
    assert review["proof_object_constructed"] is False
    assert review["conservation_proof_object_constructed"] is False
    assert review["conservation_witness_constructed"] is False
    assert review["Bianchi_compatibility_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["release_assembly_authorized"] is False
    assert review["public_submission_authorized"] is False


def test_qft_gr_limit_interchange_attempt_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_limit_interchange_regularization_boundary_assumption_reduction_attempt_result_review(
        attempt_path=ATTEMPT_PATH,
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
        LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_ID,
        BOUNDED_LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY_CONTRACT_STATUS,
        "MR-ASSUMP-004-limit_interchange_regularization_boundary",
        NEXT_ROW_ID,
        NEXT_TARGET,
    ]:
        assert token in joined
