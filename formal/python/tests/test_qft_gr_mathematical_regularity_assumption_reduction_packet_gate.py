from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_mathematical_regularity_assumption_reduction_packet_report import (
    BLOCKER,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_FAMILY_MAP_PATH,
    DEFAULT_OUT,
    DEFAULT_RESULT_REVIEW_PATH,
    DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY,
    DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN,
    LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIOR_COMPLETED_FAMILIES,
    SCHEMA_ID,
    SELECTED_ASSUMPTION_FAMILY,
    SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW,
    WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE,
    build_qft_gr_mathematical_regularity_assumption_reduction_packet,
)
from formal.python.tools.qft_gr_state_domain_assumption_reduction_closeout_packet_result_review_report import (
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as RESULT_REVIEW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_mathematical_regularity_assumption_reduction_packet_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_MathematicalRegularityAssumptionReductionPacket.lean"
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


def test_qft_gr_mathematical_regularity_packet_files_exist() -> None:
    assert DEFAULT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_FAMILY_MAP_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_mathematical_regularity_packet_consumes_state_domain_closeout_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(DEFAULT_RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert (
        packet[
            "consumes_qft_gr_state_domain_assumption_reduction_closeout_packet_result_review"
        ]
        == RESULT_REVIEW_ID
    )
    assert packet["consumed_result_review_outcome_id"] == RESULT_REVIEW_OUTCOME
    assert packet["consumed_result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["selected_next_target"] == (
        "prepare_qft_gr_mathematical_regularity_assumption_reduction_packet"
    )


def test_qft_gr_mathematical_regularity_packet_records_completed_families() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocker"] == BLOCKER
    assert packet["selected_blocker"] == BLOCKER
    assert packet["conservation_blocker_remains"] is True
    assert packet["completed_prior_assumption_families"] == PRIOR_COMPLETED_FAMILIES
    assert packet["completed_prior_assumption_family_count"] == 3
    assert packet["operator_domain_assumptions_completed"] is True
    assert packet["renormalization_assumptions_completed"] is True
    assert packet["state_domain_assumptions_completed"] is True
    assert packet["accepted_state_domain_assumption_row_count"] == 3
    assert packet["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert packet["primary_assumption_reduction_family"] == SELECTED_ASSUMPTION_FAMILY
    assert packet["selected_family_only"] is True


def test_qft_gr_mathematical_regularity_packet_selects_only_first_row() -> None:
    packet = _json(DEFAULT_OUT)
    rows = packet["mathematical_regularity_assumption_rows"]
    selected = packet["selected_mathematical_regularity_assumption"]
    assert packet["mathematical_regularity_assumption_inventory_prepared"] is True
    assert packet["mathematical_regularity_assumption_row_count"] == 4
    assert rows[0]["assumption_id"] == SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
    assert packet["selected_mathematical_regularity_assumption_row"] == (
        SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
    )
    assert packet["selected_bounded_mathematical_regularity_assumption_row"] == (
        SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
    )
    assert packet["selected_row_count"] == 1
    assert packet["selected_row_is_first_repo_authoritative_row"] is True
    assert selected["assumption_id"] == SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW
    assert selected["assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert selected["regularity_condition"] == DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY


def test_qft_gr_mathematical_regularity_packet_prepares_requested_fields_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["derivative_exchange_regular_boundary"] == (
        DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY
    )
    assert packet["weak_strong_conservation_comparison_scope"] == (
        WEAK_STRONG_CONSERVATION_COMPARISON_SCOPE
    )
    assert packet["distributional_pairing_regular_domain"] == (
        DISTRIBUTIONAL_PAIRING_REGULAR_DOMAIN
    )
    assert packet["limit_interchange_regularization_boundary"] == (
        LIMIT_INTERCHANGE_REGULARIZATION_BOUNDARY
    )
    assert packet["available_repo_evidence"]
    assert packet["required_future_proof_objects"]
    assert packet["candidate_reducible_assumptions"]
    assert packet["candidate_reducible_assumption_count"] == 4
    assert packet["not_reducible_in_current_lane"]
    assert packet["not_reducible_in_current_lane_count"] == 9
    assert packet["prepares_reduction_analysis_only"] is True
    assert packet["claim_ceiling"]
    assert packet["failure_mode_if_unresolved"]
    for row in packet["candidate_reducible_assumptions"]:
        assert row["assumption_family"] == SELECTED_ASSUMPTION_FAMILY
        assert row["available_repo_evidence"]
        assert row["required_future_proof_object"]
        assert row["candidate_reduction_route"]
        assert row["claim_ceiling"]
        assert row["failure_mode_if_unresolved"]


def test_qft_gr_mathematical_regularity_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["mathematical_regularity_assumptions_discharged"] is False
    assert (
        packet[
            "mathematical_regularity_assumptions_reduced_or_discharged_by_preparation"
        ]
        is False
    )
    assert packet["assumptions_reduced_or_discharged_by_preparation"] is False
    assert packet["state_admissibility_claimed"] is False
    assert packet["source_admissibility_claimed"] is False
    assert packet["stress_energy_source_admissibility_claimed"] is False
    assert packet["conservation_proved"] is False
    assert packet["actual_conservation_claimed"] is False
    assert packet["proof_object_constructed"] is False
    assert packet["conservation_proof_object_constructed"] is False
    assert packet["conservation_witness_constructed"] is False
    assert packet["Bianchi_compatibility_claimed"] is False
    assert packet["semiclassical_einstein_equation_derived"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["master_action_promoted"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["public_submission_authorized"] is False


def test_qft_gr_mathematical_regularity_packet_selects_one_review_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_qft_gr_derivative_exchange_regular_boundary_assumption_reduction_attempt": (
            "deferred"
        ),
        "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet": (
            "not_authorized_current_lane"
        ),
        "prepare_qft_gr_physical_source_admissibility_assumption_reduction_packet": (
            "not_authorized_current_lane"
        ),
        "construct_qft_gr_conservation_proof_object": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_state_admissibility": "not_authorized",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_release_assembly_or_public_submission": "not_authorized",
    }


def test_qft_gr_mathematical_regularity_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_mathematical_regularity_assumption_reduction_packet(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        family_map_path=DEFAULT_FAMILY_MAP_PATH,
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
        SELECTED_ASSUMPTION_FAMILY,
        SELECTED_BOUNDED_MATHEMATICAL_REGULARITY_ROW,
        DERIVATIVE_EXCHANGE_REGULAR_BOUNDARY,
        NEXT_TARGET,
    ]:
        assert token in joined
