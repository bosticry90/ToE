from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_proof_object_attempt_report import (
    DEFAULT_OUT,
    EXECUTION_CLASSIFICATIONS,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_CLASSIFICATION,
    SCHEMA_ID,
    ATTEMPT_ID,
    build_qft_gr_covariant_conservation_proof_object_attempt,
)
from formal.python.tools.qft_gr_covariant_conservation_proof_object_packet_report import (
    SELECTED_OBSTRUCTION,
    TARGET_PROOF_OBJECT,
)
from formal.python.tools.qft_gr_covariant_conservation_proof_object_packet_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as RESULT_REVIEW_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationProofObjectAttempt.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_covariant_conservation_proof_object_attempt_report.py"
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


def test_qft_gr_covariant_conservation_proof_object_attempt_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()


def test_qft_gr_covariant_conservation_proof_object_attempt_consumes_review() -> None:
    attempt = _json(DEFAULT_OUT)
    review = _json(RESULT_REVIEW_PATH)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert attempt["executed"] is True
    assert attempt["outcome_id"] == OUTCOME_ID
    assert review["review_id"] == RESULT_REVIEW_ID
    assert review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION


def test_qft_gr_covariant_conservation_proof_object_attempt_records_one_classification() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["result_classification"] == RESULT_CLASSIFICATION
    assert attempt["classification_options"] == EXECUTION_CLASSIFICATIONS
    assert attempt["result_classification_count"] == 1
    assert sum(1 for row in attempt["classification_rows"] if row["selected"]) == 1
    assert attempt["constructed_proof_object_result"] is False
    assert attempt["obstruction_identified_result"] is True
    assert attempt["inconclusive_result"] is False


def test_qft_gr_covariant_conservation_proof_object_attempt_preserves_nonclaims() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["selected_obstruction"] == SELECTED_OBSTRUCTION
    assert attempt["target_proof_object"] == TARGET_PROOF_OBJECT
    assert attempt["proof_object_attempt_executed"] is True
    assert attempt["conservation_proof_object_constructed"] is False
    assert attempt["proof_object_constructed_pending_result_review"] is False
    assert attempt["conservation_witness_constructed"] is False
    assert attempt["conservation_witness_upgraded_by_execution"] is False
    assert attempt["stress_energy_source_admissibility_claimed"] is False
    assert attempt["Bianchi_compatibility_claimed"] is False
    assert attempt["semiclassical_einstein_equation_derived"] is False
    assert attempt["qft_gr_seam_closed"] is False
    assert attempt["empirical_validation_claimed"] is False
    assert attempt["master_action_promoted"] is False
    assert attempt["release_assembly_authorized"] is False
    assert attempt["public_submission_authorized"] is False


def test_qft_gr_covariant_conservation_proof_object_attempt_selects_one_review_target() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in attempt["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet": "deferred",
        "prepare_qft_gr_covariant_conservation_proof_object_assumption_reduction_packet": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_covariant_conservation_proof_object_attempt_deterministic_and_pinned() -> None:
    attempt = _json(DEFAULT_OUT)
    generated = build_qft_gr_covariant_conservation_proof_object_attempt(
        review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert attempt == generated
    for key, value in attempt["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            SURFACES_PATH,
            REGISTRY_PATH,
            ROADMAP_PATH,
            LEAN_ATTEMPT_PATH,
            V01_INDEX_PATH,
            FRONTIER_PATH,
        ]
    )
    for token in [ATTEMPT_ID, OUTCOME_ID, RESULT_CLASSIFICATION, NEXT_TARGET]:
        assert token in joined
