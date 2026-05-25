from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_OUT,
    FUTURE_EXECUTION_CLASSIFICATIONS,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    POST_PACKET_REVIEW_TARGET,
    REQUIRED_PACKET_FIELDS,
    SCHEMA_ID,
    build_qft_gr_covariant_conservation_statement_witness_packet,
)
from formal.python.tools.qft_gr_stress_energy_conservation_obstruction_refinement_packet_report import (
    DEFAULT_OUT as REFINEMENT_PACKET_PATH,
    NEXT_TARGET as REFINEMENT_SELECTED_TARGET,
    OUTCOME_ID as REFINEMENT_OUTCOME,
    PACKET_ID as REFINEMENT_PACKET_ID,
    PRIMARY_MISSING_CONDITION,
)
from formal.python.tools.qft_gr_stress_energy_conservation_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantConservationStatementWitnessPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_covariant_conservation_statement_witness_packet_report.py"
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


def test_qft_gr_covariant_conservation_statement_witness_packet_files_exist() -> None:
    assert REFINEMENT_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_covariant_conservation_statement_witness_packet_consumes_refinement_packet() -> None:
    packet = _json(DEFAULT_OUT)
    refinement = _json(REFINEMENT_PACKET_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert refinement["packet_id"] == REFINEMENT_PACKET_ID
    assert refinement["outcome_id"] == REFINEMENT_OUTCOME
    assert refinement["selected_next_target"] == REFINEMENT_SELECTED_TARGET
    assert packet["primary_blocker"] == PRIMARY_MISSING_CONDITION


def test_qft_gr_covariant_conservation_statement_witness_packet_fields() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["required_packet_fields"] == REQUIRED_PACKET_FIELDS
    assert set(packet["packet_fields"]) == set(REQUIRED_PACKET_FIELDS)
    assert packet["packet_fields"]["current_obstruction"] == PRIMARY_MISSING_CONDITION
    assert packet["packet_fields"]["post_packet_review_target"] == POST_PACKET_REVIEW_TARGET
    assert packet["future_execution_classifications"] == FUTURE_EXECUTION_CLASSIFICATIONS


def test_qft_gr_covariant_conservation_statement_witness_packet_preserves_nonclaim_boundaries() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["conservation_witness_constructed"] is False
    assert packet["stress_energy_source_admissibility_claimed"] is False
    assert packet["Bianchi_compatibility_claimed"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["semiclassical_einstein_equation_derived"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["scientific_validation_claimed"] is False
    assert packet["master_action_promoted"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["public_submission_authorized"] is False


def test_qft_gr_covariant_conservation_statement_witness_packet_selects_one_next_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == POST_PACKET_REVIEW_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        POST_PACKET_REVIEW_TARGET: "selected",
        "execute_qft_gr_covariant_conservation_statement_witness_attempt": "deferred",
        "prepare_qft_gr_renormalized_expectation_domain_conservation_packet": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_covariant_conservation_statement_witness_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_covariant_conservation_statement_witness_packet(
        refinement_packet_path=REFINEMENT_PACKET_PATH,
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
    for token in [PACKET_ID, OUTCOME_ID, PACKET_CLASSIFICATION, POST_PACKET_REVIEW_TARGET]:
        assert token in joined
