from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_assumption_reduction_packet_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    PRIMARY_BLOCKER,
    RESULT_REVIEW_CLASSIFICATION,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIMARY_ASSUMPTION_FAMILY,
    ROW_STATUS_ENUM,
    SCHEMA_ID,
    build_qft_gr_operator_domain_assumption_reduction_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_OperatorDomainAssumptionReductionPacket.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_operator_domain_assumption_reduction_packet_report.py"
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


def test_qft_gr_operator_domain_assumption_reduction_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_operator_domain_assumption_reduction_packet_consumes_result_review() -> None:
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
    assert review["selected_next_target"] == (
        "prepare_qft_gr_operator_domain_assumption_reduction_packet"
    )


def test_qft_gr_operator_domain_assumption_reduction_packet_rows_are_explicit() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocker"] == PRIMARY_BLOCKER
    assert packet["selected_blocker"] == PRIMARY_BLOCKER
    assert packet["primary_assumption_reduction_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert packet["row_status_enum"] == ROW_STATUS_ENUM
    rows = packet["operator_domain_assumption_rows"]
    assert packet["operator_domain_assumption_row_count"] == 6
    assert [row["assumption_id"] for row in rows] == [
        "OD-ASSUMP-001-selected_operator_action",
        "OD-ASSUMP-002-candidate_source_domain_membership",
        "OD-ASSUMP-003-state_expectation_domain_link",
        "OD-ASSUMP-004-renormalized_expectation_domain_link",
        "OD-ASSUMP-005-conservation_form_scope",
        "OD-ASSUMP-006-metric_connection_scope",
    ]
    required_fields = {
        "assumption_id",
        "assumption_family",
        "current_status",
        "available_repo_evidence",
        "required_future_proof_object",
        "reduction_route",
        "claim_ceiling",
        "failure_mode_if_unresolved",
    }
    for row in rows:
        assert set(row) == required_fields
        assert row["assumption_family"] == PRIMARY_ASSUMPTION_FAMILY
        assert row["current_status"]
        assert all(status in ROW_STATUS_ENUM for status in row["current_status"])
        assert row["available_repo_evidence"]
        assert row["required_future_proof_object"]
        assert row["reduction_route"]
        assert row["claim_ceiling"]
        assert row["failure_mode_if_unresolved"]


def test_qft_gr_operator_domain_assumption_reduction_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["operator_domain_assumption_inventory_prepared"] is True
    assert packet["operator_domain_assumption_reduction_analysis_prepared"] is True
    assert packet["assumptions_reduced_or_discharged_by_preparation"] is False
    assert packet["proof_object_constructed"] is False
    assert packet["conservation_proof_object_constructed"] is False
    assert packet["conservation_witness_constructed"] is False
    assert packet["stress_energy_source_admissibility_claimed"] is False
    assert packet["Bianchi_compatibility_claimed"] is False
    assert packet["semiclassical_einstein_equation_derived"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["master_action_promoted"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["public_submission_authorized"] is False


def test_qft_gr_operator_domain_assumption_reduction_packet_selects_one_review_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_state_domain_assumption_reduction_packet": "deferred",
        "prepare_qft_gr_renormalization_assumption_reduction_packet": "deferred",
        "execute_qft_gr_covariant_conservation_proof_object_attempt": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
    }


def test_qft_gr_operator_domain_assumption_reduction_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_operator_domain_assumption_reduction_packet(
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
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        PRIMARY_BLOCKER,
        PRIMARY_ASSUMPTION_FAMILY,
        NEXT_TARGET,
    ]:
        assert token in joined
