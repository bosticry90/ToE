from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_metric_connection_scope_assumption_reduction_packet_report import (
    BOUNDED_GEOMETRY_DOMAIN,
    CONNECTION_COMPATIBILITY_CONDITION,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as PACKET_PATH,
    METRIC_CONNECTION_SCOPE_OBJECT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PRIOR_ACCEPTED_ROW001,
    PRIOR_ACCEPTED_ROW002,
    PRIOR_ACCEPTED_ROW003,
    PRIOR_ACCEPTED_ROW004,
    PRIOR_ACCEPTED_ROW005,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SELECTED_ROW_ID,
)
from formal.python.tools.qft_gr_metric_connection_scope_assumption_reduction_packet_result_review_report import (
    AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_metric_connection_scope_assumption_reduction_packet_result_review,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    PRIMARY_ASSUMPTION_FAMILY,
    ROW_STATUS_ENUM,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_MetricConnectionScopeAssumptionReductionPacketResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_metric_connection_scope_assumption_reduction_packet_result_review_report.py"
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


def test_qft_gr_metric_connection_scope_assumption_reduction_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_metric_connection_scope_assumption_reduction_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert (
        review["consumes_qft_gr_metric_connection_scope_assumption_reduction_packet"]
        == PACKET_ID
    )
    assert review["consumed_packet_outcome_id"] == PACKET_OUTCOME
    assert review["consumed_packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == CONSUMED_TARGET


def test_qft_gr_metric_connection_scope_assumption_reduction_packet_result_review_confirms_row006() -> None:
    review = _json(DEFAULT_OUT)
    selected = review["metric_connection_scope_assumption"]
    assert review["blocker"] == "insufficient_assumptions_for_conservation"
    assert review["selected_blocker"] == "insufficient_assumptions_for_conservation"
    assert review["current_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert review["selected_assumption_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert review["primary_assumption_reduction_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert review["prior_accepted_operator_domain_assumption_rows"] == [
        PRIOR_ACCEPTED_ROW001,
        PRIOR_ACCEPTED_ROW002,
        PRIOR_ACCEPTED_ROW003,
        PRIOR_ACCEPTED_ROW004,
        PRIOR_ACCEPTED_ROW005,
    ]
    assert review["prior_rows001_002_003_004_005_remain_accepted"] is True
    assert review["selected_operator_domain_assumption_row"] == SELECTED_ROW_ID
    assert selected["assumption_id"] == SELECTED_ROW_ID
    assert selected["assumption_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert review["metric_connection_scope_object"] == METRIC_CONNECTION_SCOPE_OBJECT
    assert review["bounded_geometry_domain"] == BOUNDED_GEOMETRY_DOMAIN
    assert (
        review["connection_compatibility_condition"]
        == CONNECTION_COMPATIBILITY_CONDITION
    )
    assert review["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert review["metric_connection_scope_status_tokens"] == [
        "required",
        "supplied",
        "missing",
        "candidate_reducible",
    ]
    assert all(
        token in ROW_STATUS_ENUM
        for token in review["metric_connection_scope_status_tokens"]
    )


def test_qft_gr_metric_connection_scope_assumption_reduction_packet_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["packet_preparation_only_confirmed"] is True
    assert review["metric_connection_scope_packet_accepted_by_review"] is True
    assert review["metric_connection_scope_analysis_accepted"] is True
    assert review["metric_connection_scope_assumption_reduced_by_review"] is False
    assert review["metric_connection_scope_assumption_discharged"] is False
    assert review["metric_connection_scope_claimed_as_bianchi_compatibility"] is False
    assert review["bounded_geometry_domain_claimed_as_bianchi_compatibility"] is False
    assert review["connection_compatibility_claimed_as_bianchi_compatibility"] is False
    assert review["metric_connection_scope_claimed_as_conservation_proof"] is False
    assert review["actual_conservation_claimed"] is False
    assert review["covariant_conservation_statement_proved"] is False
    assert review["conservation_proved"] is False
    assert review["assumptions_reduced_or_discharged_by_review"] is False
    assert review["proof_object_constructed"] is False
    assert review["conservation_proof_object_constructed"] is False
    assert review["conservation_witness_constructed"] is False
    assert review["source_admissibility_claimed"] is False
    assert review["stress_energy_source_admissibility_claimed"] is False
    assert review["Bianchi_compatibility_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False
    assert review["release_assembly_authorized"] is False
    assert review["public_submission_authorized"] is False


def test_qft_gr_metric_connection_scope_assumption_reduction_packet_result_review_selects_one_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selection_count"] == 1
    assert review["bounded_reduction_attempt_authorized"] is True
    assert review["authorized_attempt_result_classifications"] == (
        AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS
    )
    assert review["authorized_attempt_result_classification_count"] == 3
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_qft_gr_covariant_conservation_proof_object_attempt": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "prepare_qft_gr_source_admissibility_assumption_reduction_packet": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_metric_connection_scope_assumption_reduction_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_metric_connection_scope_assumption_reduction_packet_result_review(
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
    for token in [
        REVIEW_ID,
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        SELECTED_ROW_ID,
        METRIC_CONNECTION_SCOPE_OBJECT,
        BOUNDED_GEOMETRY_DOMAIN,
        CONNECTION_COMPATIBILITY_CONDITION,
        REQUIRED_FUTURE_PROOF_OBJECT,
        NEXT_TARGET,
    ]:
        assert token in joined
