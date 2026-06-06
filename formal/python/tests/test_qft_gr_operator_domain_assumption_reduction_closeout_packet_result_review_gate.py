from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_metric_connection_scope_assumption_reduction_packet_report import (
    PRIOR_ACCEPTED_ROW001,
    PRIOR_ACCEPTED_ROW002,
    PRIOR_ACCEPTED_ROW003,
    PRIOR_ACCEPTED_ROW004,
    PRIOR_ACCEPTED_ROW005,
    SELECTED_ROW_ID as ACCEPTED_ROW006,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_closeout_packet_report import (
    DEFAULT_OUT as PACKET_PATH,
    OUTCOME_ID as PACKET_OUTCOME,
)
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_report import (
    BLOCKER,
    CONSUMED_TARGET,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    NEXT_ASSUMPTION_FAMILY,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_OperatorDomainAssumptionReductionCloseoutPacketResultReview.lean"
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


def _accepted_rows() -> list[str]:
    return [
        PRIOR_ACCEPTED_ROW001,
        PRIOR_ACCEPTED_ROW002,
        PRIOR_ACCEPTED_ROW003,
        PRIOR_ACCEPTED_ROW004,
        PRIOR_ACCEPTED_ROW005,
        ACCEPTED_ROW006,
    ]


def test_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_packet_outcome_id"] == PACKET_OUTCOME
    assert packet["selected_next_target"] == CONSUMED_TARGET


def test_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_accepts_rows_for_lane_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["accepted_operator_domain_assumption_rows"] == _accepted_rows()
    assert review["accepted_operator_domain_assumption_row_count"] == 6
    assert review["operator_domain_assumptions_closed_for_this_lane"] is True
    assert review["operator_domain_assumptions_reduced_for_this_lane"] is True
    assert review["operator_domain_assumption_reduction_family_reduced"] is True
    assert review["operator_domain_assumption_reduction_closeout_packet_reviewed"] is True
    assert review["operator_domain_assumption_reduction_closeout_accepted"] is True
    assert review["operator_domain_assumption_reduction_closeout_rejected"] is False
    assert review["blocker"] == BLOCKER
    assert review["conservation_blocker_remains"] is True
    assert review["broader_blocker_resolution_required"] is True


def test_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    assert review["conservation_proved"] is False
    assert review["actual_conservation_claimed"] is False
    assert review["covariant_conservation_statement_proved"] is False
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
    assert review["master_action_promotion_authorized"] is False
    assert review["release_assembly_authorized"] is False
    assert review["public_submission_authorized"] is False
    assert review["assumption_discharge_claimed"] is False
    assert review["assumptions_discharged_by_closeout_review"] is False
    assert review["assumptions_reduced_or_discharged_by_closeout_review"] is False


def test_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_selects_next_family_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["assumption_family_selection_authorized"] is True
    assert review["next_assumption_family"] == NEXT_ASSUMPTION_FAMILY
    assert review["next_assumption_family_selection_only"] is True
    assert review["renormalization_assumption_reduction_packet_authorized"] is True
    assert review["state_domain_assumption_reduction_packet_deferred"] is True
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_state_domain_assumption_reduction_packet": "deferred",
        "execute_qft_gr_covariant_conservation_proof_object_attempt": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
    }


def test_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = (
        build_qft_gr_operator_domain_assumption_reduction_closeout_packet_result_review(
            packet_path=PACKET_PATH,
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
        "operator_domain_assumptions_closed_for_this_lane",
        "OD-ASSUMP-006-metric_connection_scope",
        NEXT_TARGET,
    ]:
        assert token in joined
