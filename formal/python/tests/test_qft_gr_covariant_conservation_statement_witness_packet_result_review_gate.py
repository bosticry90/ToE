from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_OUT as PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    EXECUTION_CLASSIFICATIONS,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_covariant_conservation_statement_witness_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationStatementWitnessPacketResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_covariant_conservation_statement_witness_packet_result_review_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
CURRENT_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
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


def _json(path: Path) -> dict:
    assert path.exists(), f"Missing JSON artifact: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _text(path: Path) -> str:
    assert path.exists(), f"Missing text artifact: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_gr_covariant_conservation_statement_witness_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["result_review_classification_count"] == 1
    assert (
        review["consumes_qft_gr_covariant_conservation_statement_witness_packet"]
        == PACKET_ID
    )
    assert review["consumed_packet_outcome_id"] == PACKET_OUTCOME
    assert review["consumed_packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == (
        "review_qft_gr_covariant_conservation_statement_witness_packet_result"
    )


def test_qft_gr_covariant_conservation_statement_witness_packet_result_review_gate_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["primary_blocker"] == "missing_covariant_conservation_statement"
    assert review["primary_missing_condition"] == "missing_covariant_conservation_statement"
    assert review["packet_preparation_only_confirmed"] is True
    for key in [
        "conservation_witness_constructed",
        "stress_energy_source_admissibility_claimed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_seam_closed",
        "empirical_validation_claimed",
        "scientific_validation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "release_assembly_authorized",
        "release_packet_assembled",
        "public_submission_authorized",
        "publication_authorized",
    ]:
        assert review[key] is False


def test_qft_gr_covariant_conservation_statement_witness_packet_result_review_selects_attempt() -> None:
    review = _json(DEFAULT_OUT)
    assert review["bounded_witness_attempt_authorized"] is True
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "qft_gr_covariant_conservation_statement_witness_attempt_execution"
    )
    assert review["selection_count"] == 1
    assert review["future_execution_classifications"] == EXECUTION_CLASSIFICATIONS
    assert [
        row for row in review["candidate_next_targets"] if row["decision"] == "selected"
    ] == [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The covariant-conservation statement witness packet is accepted, so only the bounded witness attempt is authorized.",
        }
    ]


def test_qft_gr_covariant_conservation_statement_witness_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_covariant_conservation_statement_witness_packet_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert review == generated
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    for path in [TOOL_PATH, LEAN_REVIEW_PATH, V01_INDEX_PATH, FRONTIER_PATH]:
        text = _text(path)
        assert OUTCOME_ID in text
        assert NEXT_TARGET in text
    for path in [REGISTRY_PATH, CURRENT_SURFACES_PATH]:
        text = _text(path)
        assert OUTCOME_ID in text
        assert NEXT_TARGET in text
        assert "review_qft_gr_covariant_conservation_statement_witness_packet_result" in text
