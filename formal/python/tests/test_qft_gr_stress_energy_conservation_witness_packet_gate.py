from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review_report import (
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as RESULT_REVIEW_ID,
)
from formal.python.tools.qft_gr_stress_energy_conservation_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POST_PACKET_REVIEW_TARGET,
    SCHEMA_ID,
    build_qft_gr_stress_energy_conservation_witness_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_OBSTRUCTION_REFINEMENT_PACKET_RESULT_REVIEW_20260525_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_StressEnergyConservationWitnessPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_stress_energy_conservation_witness_packet_report.py"
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


def test_qft_gr_stress_energy_conservation_witness_packet_fields() -> None:
    packet = _json(DEFAULT_OUT)
    result_review = _json(RESULT_REVIEW_PATH)

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["packet_classification_count"] == 1
    assert (
        packet[
            "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_obstruction_refinement_packet_result_review"
        ]
        == RESULT_REVIEW_ID
    )
    assert packet["consumed_result_review_outcome_id"] == RESULT_REVIEW_OUTCOME
    assert (
        packet["consumed_result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    )
    assert result_review["primary_missing_condition"] == "conservation"
    assert packet["primary_missing_condition"] == "conservation"
    assert packet["primary_obstruction_preserved"] is True


def test_qft_gr_stress_energy_conservation_witness_packet_required_fields() -> None:
    packet = _json(DEFAULT_OUT)
    for field in [
        "source_object",
        "renormalization_scope",
        "state_expectation_scope",
        "conservation_statement",
        "covariant_or_weak_conservation_form",
        "domain_of_validity",
        "Bianchi_compatibility_dependency",
        "required_Lean_surfaces",
        "required_math_assumptions",
        "required_physics_assumptions",
        "failure_modes",
        "claim_ceiling",
        "forbidden_claims",
        "post_packet_review_target",
    ]:
        assert field in packet
        assert packet[field]
    assert packet["post_packet_review_target"] == POST_PACKET_REVIEW_TARGET
    assert packet["selected_next_target"] == POST_PACKET_REVIEW_TARGET
    assert packet["selection_count"] == 1
    assert packet["selected_next_target_kind"] == (
        "qft_gr_stress_energy_conservation_witness_packet_result_review"
    )


def test_qft_gr_stress_energy_conservation_witness_packet_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
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
        assert packet[key] is False
    assert "conservation_witness_constructed" in packet["forbidden_claims"]
    assert "stress_energy_source_admissibility_claimed" in packet["forbidden_claims"]
    assert "Bianchi_compatibility_claimed" in packet["forbidden_claims"]


def test_qft_gr_stress_energy_conservation_witness_packet_future_classifications() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["future_execution_classifications"] == [
        "qft_gr_stress_energy_conservation_witness_constructed_pending_result_review",
        "qft_gr_stress_energy_conservation_obstruction_identified_requires_refinement",
        "qft_gr_stress_energy_conservation_inconclusive_requires_assumption_reduction",
    ]
    assert [
        row for row in packet["candidate_next_targets"] if row["decision"] == "selected"
    ] == [
        {
            "target": POST_PACKET_REVIEW_TARGET,
            "decision": "selected",
            "reason": "Packet preparation must be reviewed before a conservation witness attempt is authorized.",
        }
    ]


def test_qft_gr_stress_energy_conservation_witness_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_stress_energy_conservation_witness_packet(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert packet == generated

    for path in [TOOL_PATH, LEAN_PACKET_PATH, V01_INDEX_PATH, FRONTIER_PATH]:
        text = _text(path)
        assert OUTCOME_ID in text
        assert POST_PACKET_REVIEW_TARGET in text
    for path in [REGISTRY_PATH, CURRENT_SURFACES_PATH]:
        text = _text(path)
        assert OUTCOME_ID in text
        assert POST_PACKET_REVIEW_TARGET in text
        assert "prepare_qft_gr_stress_energy_conservation_witness_packet" in text
