from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_renormalization_assumption_reduction_closeout_packet_report import (
    BLOCKER,
    CLOSEOUT_CLASSIFICATION,
    CONSUMED_TARGET,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_ID,
    SCHEMA_ID,
    SELECTED_ASSUMPTION_FAMILY,
    build_qft_gr_renormalization_assumption_reduction_closeout_packet,
)
from formal.python.tools.qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as RESULT_REVIEW_ID,
)
from formal.python.tools.qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet_report import (
    ACCEPTED_PRIOR_ROWS,
    SELECTED_ROW_ID as ACCEPTED_ROW005,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_renormalization_assumption_reduction_closeout_packet_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_RenormalizationAssumptionReductionCloseoutPacket.lean"
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
    return [*ACCEPTED_PRIOR_ROWS, ACCEPTED_ROW005]


def test_qft_gr_renormalization_assumption_reduction_closeout_packet_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_renormalization_assumption_reduction_closeout_packet_consumes_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    result_review = _json(RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["closeout_classification"] == CLOSEOUT_CLASSIFICATION
    assert (
        packet[
            "consumes_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review"
        ]
        == RESULT_REVIEW_ID
    )
    assert packet["consumed_result_review_outcome_id"] == RESULT_REVIEW_OUTCOME
    assert packet["consumed_result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert result_review["selected_next_target"] == CONSUMED_TARGET


def test_qft_gr_renormalization_assumption_reduction_closeout_packet_records_all_five_rows() -> None:
    packet = _json(DEFAULT_OUT)
    rows = _accepted_rows()
    assert packet["accepted_renormalization_assumption_rows"] == rows
    assert packet["accepted_renormalization_assumption_row_count"] == 5
    assert packet["renormalization_assumption_row_count"] == 5
    assert packet["renormalization_assumptions_row_sequence_completed"] is True
    assert packet["renormalization_assumption_rows"] == [
        {
            "row_id": row,
            "status": "accepted",
            "source": source,
        }
        for row, source in zip(
            rows,
            [
                "qft_gr_renormalized_stress_energy_object_assumption_reduction_attempt_result_review_v0",
                "qft_gr_renormalization_scope_assumption_reduction_attempt_result_review_v0",
                "qft_gr_renormalized_expectation_domain_assumption_reduction_attempt_result_review_v0",
                "qft_gr_renormalized_expectation_finiteness_assumption_reduction_attempt_result_review_v0",
                "qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_attempt_result_review_v0",
            ],
            strict=True,
        )
    ]
    assert packet["renormalization_assumptions_reduced_for_this_lane"] is True
    assert packet["renormalization_assumption_reduction_family_reduced"] is True
    assert packet["renormalization_assumption_reduction_row_inventory_exhausted"] is True
    assert packet["no_remaining_renormalization_assumption_row_in_current_inventory"] is True
    assert packet["next_renormalization_assumption_row"] is None


def test_qft_gr_renormalization_assumption_reduction_closeout_packet_preserves_blocker_and_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["blocker"] == BLOCKER
    assert packet["selected_blocker"] == BLOCKER
    assert packet["blocker_remains"] == BLOCKER
    assert packet["selected_assumption_family"] == SELECTED_ASSUMPTION_FAMILY
    assert packet["conservation_blocker_remains"] is True
    assert packet["downstream_review_or_adjudication_required"] is True
    assert packet["renormalization_assumptions_family_closeout_prepared"] is True
    assert packet["renormalization_assumption_reduction_closeout_packet_prepared"] is True
    assert packet["renormalization_assumption_reduction_closeout_prepared"] is True
    assert packet["renormalization_assumption_reduction_closeout_status"] == (
        "prepared_pending_result_review"
    )
    assert packet["renormalization_assumption_reduction_closeout_result_review_required"] is True
    assert packet["renormalization_assumption_reduction_closeout_preparation_only"] is True
    assert packet["conservation_proved"] is False
    assert packet["actual_conservation_claimed"] is False
    assert packet["covariant_conservation_statement_proved"] is False
    assert packet["proof_object_constructed"] is False
    assert packet["conservation_proof_object_constructed"] is False
    assert packet["conservation_witness_constructed"] is False
    assert packet["source_admissibility_claimed"] is False
    assert packet["stress_energy_source_admissibility_claimed"] is False
    assert packet["Bianchi_compatibility_claimed"] is False
    assert packet["semiclassical_einstein_equation_derived"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["master_action_promoted"] is False
    assert packet["master_action_promotion_authorized"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["public_submission_authorized"] is False
    assert packet["assumption_discharge_claimed"] is False
    assert packet["assumptions_discharged_by_closeout"] is False
    assert packet["assumptions_reduced_or_discharged_by_closeout"] is False
    assert packet["renormalization_assumptions_discharged_by_closeout"] is False
    assert (
        packet["renormalization_assumptions_reduced_or_discharged_by_closeout"]
        is False
    )


def test_qft_gr_renormalization_assumption_reduction_closeout_packet_selects_result_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["renormalization_assumption_reduction_closeout_packet_selected_next_target"] == NEXT_TARGET
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "select_next_renormalization_assumption_row": "not_authorized",
        "construct_qft_gr_conservation_proof_object": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_release_assembly_or_public_submission": "not_authorized",
    }


def test_qft_gr_renormalization_assumption_reduction_closeout_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_renormalization_assumption_reduction_closeout_packet(
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
        CLOSEOUT_CLASSIFICATION,
        "renormalization_assumptions_row_sequence_completed",
        "RN-ASSUMP-005-operator_domain_compatibility",
        NEXT_TARGET,
    ]:
        assert token in joined
