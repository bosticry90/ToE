from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_proof_object_attempt_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PROOF_OBJECT_OBSTRUCTION_CLASS,
    RESULT_REVIEW_CLASSIFICATION,
)
from formal.python.tools.qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_report import (
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIMARY_BLOCKER,
    SCHEMA_ID,
    build_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet,
)
from formal.python.tools.qft_gr_covariant_conservation_proof_object_packet_report import (
    SELECTED_OBSTRUCTION,
    TARGET_PROOF_OBJECT,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationProofObjectObstructionRefinementPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_report.py"
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


def test_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_consumes_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_result_review_outcome_id"] == RESULT_REVIEW_OUTCOME
    assert packet["consumed_result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["selected_next_target"] == "prepare_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet"


def test_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_narrows_blocker() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["proof_object_obstruction_class"] == PROOF_OBJECT_OBSTRUCTION_CLASS
    assert packet["selected_obstruction"] == SELECTED_OBSTRUCTION
    assert packet["target_proof_object"] == TARGET_PROOF_OBJECT
    assert packet["blocker_menu"] == [
        "missing_theorem_shape",
        PRIMARY_BLOCKER,
        "operator_domain_still_too_weak",
        "renormalized_expectation_not_compatible_with_derivative_action",
        "state_domain_limitation",
        "weak_strong_conservation_mismatch",
        "Bianchi_compatibility_dependency_still_unresolved",
    ]
    assert packet["blocker_menu_count"] == 7
    assert packet["primary_blocker"] == PRIMARY_BLOCKER
    assert packet["selected_primary_blocker"] == PRIMARY_BLOCKER
    assert packet["identifies_proof_object_obstruction_more_narrowly"] is True
    assert packet["prepares_refinement_only"] is True


def test_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["proof_object_constructed"] is False
    assert packet["conservation_proof_object_constructed"] is False
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


def test_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_selects_one_review_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_covariant_conservation_assumptions_packet": "deferred",
        "execute_qft_gr_covariant_conservation_proof_object_attempt": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet(
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
    for token in [PACKET_ID, OUTCOME_ID, PACKET_CLASSIFICATION, PRIMARY_BLOCKER, NEXT_TARGET]:
        assert token in joined
