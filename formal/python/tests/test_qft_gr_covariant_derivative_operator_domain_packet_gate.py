from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_statement_obstruction_refinement_packet_report import (
    DEFAULT_OUT as REFINEMENT_PATH,
    OUTCOME_ID as REFINEMENT_OUTCOME,
    PACKET_CLASSIFICATION as REFINEMENT_CLASSIFICATION,
    PRIMARY_MISSING_CONDITION,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)
from formal.python.tools.qft_gr_covariant_derivative_operator_domain_packet_report import (
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID,
    SCIENTIFIC_QUESTION,
    build_qft_gr_covariant_derivative_operator_domain_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_CovariantDerivativeOperatorDomainPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_covariant_derivative_operator_domain_packet_report.py"
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


def test_qft_gr_covariant_derivative_operator_domain_packet_files_exist() -> None:
    assert REFINEMENT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_covariant_derivative_operator_domain_packet_consumes_refinement() -> None:
    packet = _json(DEFAULT_OUT)
    refinement = _json(REFINEMENT_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["scientific_question"] == SCIENTIFIC_QUESTION
    assert refinement["outcome_id"] == REFINEMENT_OUTCOME
    assert refinement["packet_classification"] == REFINEMENT_CLASSIFICATION
    assert packet["primary_blocker"] == PRIMARY_MISSING_CONDITION


def test_qft_gr_covariant_derivative_operator_domain_packet_requirements() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["operator_domain_structure_prepared"] is True
    assert packet["operator_domain_requirement_count"] == 6
    assert [row["requirement_id"] for row in packet["operator_domain_requirements"]] == [
        "connection_or_derivative_operator",
        "operator_domain",
        "candidate_source_codomain",
        "regularity_or_distributional_scope",
        "state_expectation_domain_link",
        "metric_or_background_scope",
    ]


def test_qft_gr_covariant_derivative_operator_domain_packet_preserves_nonclaim_boundaries() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["covariant_conservation_statement_formulated"] is False
    assert packet["covariant_conservation_statement_attempted"] is False
    assert packet["covariant_conservation_statement_witness_constructed"] is False
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


def test_qft_gr_covariant_derivative_operator_domain_packet_selects_one_review_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_covariant_conservation_statement_with_operator_domain_packet": "deferred",
        "prepare_qft_gr_renormalized_expectation_domain_conservation_packet": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_covariant_derivative_operator_domain_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_covariant_derivative_operator_domain_packet(
        refinement_path=REFINEMENT_PATH,
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
