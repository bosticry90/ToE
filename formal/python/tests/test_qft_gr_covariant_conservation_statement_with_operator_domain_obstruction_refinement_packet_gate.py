from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_report import (
    AVAILABLE_STRUCTURE,
    CLAIM_CEILING,
    DEFAULT_OUT,
    FAILURE_MODE_IF_UNRESOLVED,
    MISSING_PROOF_OBJECT,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIMARY_MISSING_CONDITION,
    PRIMARY_OBSTRUCTION_ID,
    REQUIRED_ASSUMPTIONS,
    REQUIRED_LEAN_SURFACE,
    REQUIRED_THEOREM_SHAPE,
    SCHEMA_ID,
    build_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_with_operator_domain_witness_attempt_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    REFINED_OBSTRUCTION_CLASS,
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
    / "QFT_GR_CovariantConservationStatementWithOperatorDomainObstructionRefinementPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_report.py"
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


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_consumes_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert review["review_id"] == RESULT_REVIEW_ID
    assert review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert packet["selected_obstruction"] == REFINED_OBSTRUCTION_CLASS


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_defines_missing_proof_object() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_obstruction"] == PRIMARY_MISSING_CONDITION
    assert packet["available_structure"] == AVAILABLE_STRUCTURE
    assert packet["missing_proof_object"] == MISSING_PROOF_OBJECT
    assert packet["required_theorem_shape"] == REQUIRED_THEOREM_SHAPE
    assert packet["required_assumptions"] == REQUIRED_ASSUMPTIONS
    assert packet["required_Lean_surface"] == REQUIRED_LEAN_SURFACE
    assert packet["failure_mode_if_unresolved"] == FAILURE_MODE_IF_UNRESOLVED
    assert packet["claim_ceiling"] == CLAIM_CEILING
    assert packet["next_bounded_action"] == NEXT_TARGET
    assert packet["primary_obstruction_id"] == PRIMARY_OBSTRUCTION_ID
    assert packet["primary_missing_condition"] == PRIMARY_MISSING_CONDITION
    assert packet["primary_obstruction_solved"] is False
    required = {
        "obstruction_id",
        "missing_condition",
        "priority",
        "available_structure",
        "required_theorem_shape",
        "required_Lean_surface",
        "required_assumptions",
        "failure_mode_if_unresolved",
        "claim_ceiling",
        "next_bounded_action",
    }
    assert all(required <= set(row) for row in packet["refinement_rows"])


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["prepares_refinement_only"] is True
    assert packet["covariant_conservation_statement_with_operator_domain_witness_constructed"] is False
    assert packet["conservation_witness_constructed"] is False
    assert packet["stress_energy_source_admissibility_claimed"] is False
    assert packet["Bianchi_compatibility_claimed"] is False
    assert packet["semiclassical_einstein_equation_derived"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["scientific_validation_claimed"] is False
    assert packet["master_action_promoted"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["public_submission_authorized"] is False


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_selects_one_review_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_covariant_conservation_proof_object_packet": "deferred",
        "prepare_qft_gr_renormalized_expectation_domain_conservation_packet": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_covariant_conservation_statement_with_operator_domain_obstruction_refinement_packet(
        result_review_path=RESULT_REVIEW_PATH,
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
    for token in [PACKET_ID, OUTCOME_ID, PACKET_CLASSIFICATION, NEXT_TARGET]:
        assert token in joined
