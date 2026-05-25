from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_report import (
    DEFAULT_OUT as PACKET_PATH,
    MISSING_PROOF_OBJECT,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIMARY_MISSING_CONDITION,
    REQUIRED_ASSUMPTIONS,
    REQUIRED_LEAN_SURFACE,
    REQUIRED_THEOREM_SHAPE,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_report import (
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationStatementWithOperatorDomainObstructionRefinementPacketResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_report.py"
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


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert (
        review[
            "consumes_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet"
        ]
        == PACKET_ID
    )
    assert packet["outcome_id"] == PACKET_OUTCOME
    assert packet["packet_classification"] == PACKET_CLASSIFICATION


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_accepts_missing_proof_object() -> None:
    review = _json(DEFAULT_OUT)
    assert review["obstruction_refinement_packet_result_reviewed"] is True
    assert review["missing_conservation_proof_object_accepted"] is True
    assert review["selected_obstruction"] == PRIMARY_MISSING_CONDITION
    assert review["missing_proof_object"] == MISSING_PROOF_OBJECT
    assert review["required_theorem_shape"] == REQUIRED_THEOREM_SHAPE
    assert review["required_assumptions"] == REQUIRED_ASSUMPTIONS
    assert review["required_Lean_surface"] == REQUIRED_LEAN_SURFACE
    assert review["proof_object_packet_preparation_authorized"] is True


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["conservation_proof_object_constructed"] is False
    assert review["covariant_conservation_statement_with_operator_domain_witness_constructed"] is False
    assert review["conservation_witness_constructed"] is False
    assert review["stress_energy_source_admissibility_claimed"] is False
    assert review["Bianchi_compatibility_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False
    assert review["release_assembly_authorized"] is False
    assert review["public_submission_authorized"] is False


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_selects_one_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt": "deferred",
        "prepare_qft_gr_renormalized_expectation_domain_conservation_packet": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_result_review(
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
    for token in [REVIEW_ID, OUTCOME_ID, RESULT_REVIEW_CLASSIFICATION, NEXT_TARGET]:
        assert token in joined
