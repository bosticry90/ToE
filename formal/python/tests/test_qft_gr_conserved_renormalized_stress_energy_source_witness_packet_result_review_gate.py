from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_packet_report import (
    DEFAULT_OUT as PACKET_PATH,
    EXECUTION_CLASSIFICATIONS,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_ID,
)
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review_report import (
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_ConservedRenormalizedStressEnergySourceWitnessPacketResultReview.lean"
)
SURFACES_PATH = REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_qft_gr_source_witness_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_qft_gr_source_witness_packet_result_review_consumes_packet() -> None:
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
        review[
            "consumes_qft_gr_conserved_renormalized_stress_energy_source_witness_packet"
        ]
        == PACKET_ID
    )
    assert packet["outcome_id"] == PACKET_OUTCOME
    assert packet["selected_next_target"] == (
        "review_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result"
    )


def test_qft_gr_source_witness_packet_result_review_preserves_firewalls() -> None:
    review = _json(DEFAULT_OUT)
    assert review["track1_clearance_treated_as_scientific_evidence"] is False
    assert review["control_lane_clearance_only"] is True
    assert review["witness_packet_result_reviewed"] is True
    assert review["witness_packet_accepted"] is True
    assert review["witness_packet_preparation_only_confirmed"] is True
    assert review["bounded_witness_attempt_authorized"] is True
    assert review["witness_attempt_executed"] is False
    assert review["witness_constructed"] is False
    assert review["conserved_renormalized_stress_energy_source_exists_claimed"] is False
    assert review["semiclassical_einstein_equation_derived"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["qft_gr_source_map_closure_claimed"] is False
    assert review["empirical_validation_claimed"] is False
    assert review["scientific_validation_claimed"] is False
    assert review["master_action_promoted"] is False
    assert review["release_assembly_authorized"] is False
    assert review["public_submission_authorized"] is False
    assert review["source_map_seam_pillar_master_action_promotion_authorized"] is False


def test_qft_gr_source_witness_packet_result_review_selects_one_execution_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert (
        review["selected_next_target_kind"]
        == "qft_gr_conserved_renormalized_source_witness_attempt_execution_only"
    )
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "construct_qft_gr_conserved_renormalized_source_witness_as_claim": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "assemble_v01_alpha_release_packet": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }
    assert review["execution_classification_options"] == EXECUTION_CLASSIFICATIONS
    assert review["execution_classification_selected"] is None


def test_qft_gr_source_witness_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert review == generated
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    refs = [
        REVIEW_ID,
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        NEXT_TARGET,
        "formal/docs/release/QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_RESULT_REVIEW_20260525_v0.json",
        "formal/python/tools/qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review_report.py",
        "formal/python/tests/test_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result_review_gate.py",
    ]
    joined = "\n".join(
        _read(path)
        for path in [
            SURFACES_PATH,
            REGISTRY_PATH,
            ROADMAP_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            LEAN_REVIEW_PATH,
        ]
    )
    for ref in refs:
        assert ref in joined
