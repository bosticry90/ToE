from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_metric_connection_scope_assumption_reduction_attempt_report import (
    DEFAULT_OUT as ATTEMPT_PATH,
    METRIC_CONNECTION_SCOPE_CONTRACT_ID,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    RESULT_CLASSIFICATION as ATTEMPT_CLASSIFICATION,
)
from formal.python.tools.qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review,
)
from formal.python.tools.qft_gr_metric_connection_scope_assumption_reduction_packet_report import (
    BOUNDED_GEOMETRY_DOMAIN,
    CONNECTION_COMPATIBILITY_CONDITION,
    METRIC_CONNECTION_SCOPE_OBJECT,
    PRIOR_ACCEPTED_ROW001,
    PRIOR_ACCEPTED_ROW002,
    PRIOR_ACCEPTED_ROW003,
    PRIOR_ACCEPTED_ROW004,
    PRIOR_ACCEPTED_ROW005,
    REQUIRED_FUTURE_PROOF_OBJECT,
    SELECTED_ROW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_MetricConnectionScopeAssumptionReductionAttemptResultReview.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_report.py"
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


def test_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_files_exist() -> None:
    assert ATTEMPT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_consumes_attempt() -> None:
    review = _json(DEFAULT_OUT)
    attempt = _json(ATTEMPT_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_attempt_outcome_id"] == ATTEMPT_OUTCOME
    assert review["consumed_attempt_classification"] == ATTEMPT_CLASSIFICATION
    assert (
        attempt["selected_next_target"]
        == "review_qft_gr_metric_connection_scope_assumption_reduction_attempt_result"
    )


def test_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_accepts_row006_only() -> None:
    review = _json(DEFAULT_OUT)
    contract = review["metric_connection_scope_reduction_contract"]
    accepted_rows = [
        PRIOR_ACCEPTED_ROW001,
        PRIOR_ACCEPTED_ROW002,
        PRIOR_ACCEPTED_ROW003,
        PRIOR_ACCEPTED_ROW004,
        PRIOR_ACCEPTED_ROW005,
        SELECTED_ROW_ID,
    ]
    assert review["accepted_operator_domain_assumption_rows"] == accepted_rows
    assert review["prior_accepted_operator_domain_assumption_rows"] == accepted_rows[:5]
    assert review["selected_operator_domain_assumption_row"] == SELECTED_ROW_ID
    assert review["completed_operator_domain_row"] == SELECTED_ROW_ID
    assert review["accepted_contract_id"] == METRIC_CONNECTION_SCOPE_CONTRACT_ID
    assert contract["contract_id"] == METRIC_CONNECTION_SCOPE_CONTRACT_ID
    assert contract["assumption_id"] == SELECTED_ROW_ID
    assert contract["metric_connection_scope_object"] == METRIC_CONNECTION_SCOPE_OBJECT
    assert contract["bounded_geometry_domain"] == BOUNDED_GEOMETRY_DOMAIN
    assert contract["connection_compatibility_condition"] == (
        CONNECTION_COMPATIBILITY_CONDITION
    )
    assert contract["required_future_proof_object"] == REQUIRED_FUTURE_PROOF_OBJECT
    assert (
        review["metric_connection_scope_assumption_reduction_attempt_result_reviewed"]
        is True
    )
    assert review["metric_connection_scope_assumption_reduction_accepted"] is True
    assert review["metric_connection_scope_assumption_reduction_rejected"] is False
    assert review["metric_connection_scope_assumption_discharged"] is False


def test_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["operator_domain_assumptions_reduced_for_this_lane"] is True
    assert review["operator_domain_assumption_reduction_family_reduced"] is True
    assert review["metric_connection_scope_assumption_discharged"] is False
    assert review["metric_connection_scope_assumption_discharged_by_review"] is False
    assert review["metric_connection_scope_claimed_as_conservation_proof"] is False
    assert review["metric_connection_scope_claimed_as_bianchi_compatibility"] is False
    assert review["actual_conservation_claimed"] is False
    assert review["conservation_proved"] is False
    assert review["source_admissibility_claimed"] is False
    assert review["stress_energy_source_admissibility_claimed"] is False
    assert review["assumption_discharge_claimed"] is False
    assert review["assumptions_reduced_or_discharged_by_review"] is False
    assert review["assumptions_reduced_or_discharged_by_implication"] is False
    assert review["proof_object_constructed"] is False
    assert review["conservation_proof_object_constructed"] is False
    assert review["conservation_witness_constructed"] is False
    assert review["Bianchi_compatibility_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["master_action_promoted"] is False
    assert review["release_assembly_authorized"] is False
    assert review["public_submission_authorized"] is False


def test_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_selects_closeout_packet() -> None:
    review = _json(DEFAULT_OUT)
    assert review["operator_domain_assumption_reduction_closeout_packet_authorized"] is True
    assert review["operator_domain_assumption_reduction_closeout_preparation_only"] is True
    assert review["operator_domain_assumption_reduction_closeout_target"] == NEXT_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_qft_gr_covariant_conservation_proof_object_attempt": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "prepare_qft_gr_source_admissibility_assumption_reduction_packet": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = (
        build_qft_gr_metric_connection_scope_assumption_reduction_attempt_result_review(
            attempt_path=ATTEMPT_PATH,
            captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
        )
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
        METRIC_CONNECTION_SCOPE_CONTRACT_ID,
        "OD-ASSUMP-006-metric_connection_scope",
        NEXT_TARGET,
    ]:
        assert token in joined
