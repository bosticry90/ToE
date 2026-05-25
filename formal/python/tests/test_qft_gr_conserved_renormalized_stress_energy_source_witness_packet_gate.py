from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_conserved_renormalized_stress_energy_source_witness_packet_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    EXECUTION_CLASSIFICATIONS,
    EXECUTION_TARGET,
    FORBIDDEN_CLAIMS,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REQUIRED_LEAN_SURFACES,
    SCHEMA_ID,
    SCIENTIFIC_QUESTION,
    build_qft_gr_conserved_renormalized_stress_energy_source_witness_packet,
)
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_result_review_report import (
    DEFAULT_OUT as CONTROL_REVIEW_PATH,
    OUTCOME_ID as CONTROL_REVIEW_OUTCOME,
    REVIEW_ID as CONTROL_REVIEW_ID,
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
    / "qft_gr_conserved_renormalized_stress_energy_source_witness_packet_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_ConservedRenormalizedStressEnergySourceWitnessPacket.lean"
)
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
SURFACES_PATH = REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_qft_gr_conserved_renormalized_source_witness_packet_files_exist() -> None:
    assert CONTROL_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_qft_gr_conserved_renormalized_source_witness_packet_consumes_control_clearance_only() -> None:
    packet = _json(DEFAULT_OUT)
    control = _json(CONTROL_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_criticizability_readiness_result_review"] == CONTROL_REVIEW_ID
    assert control["outcome_id"] == CONTROL_REVIEW_OUTCOME
    assert control["selected_next_target"] == CONSUMED_TARGET
    assert packet["control_lane_clearance_only"] is True
    assert packet["criticizability_readiness_treated_as_scientific_evidence"] is False


def test_qft_gr_conserved_renormalized_source_witness_packet_required_fields() -> None:
    packet = _json(DEFAULT_OUT)
    required = {
        "stress_energy_object",
        "renormalization_scope",
        "state_expectation_scope",
        "finiteness_condition",
        "conservation_condition",
        "classical_source_admissibility_condition",
        "Bianchi_compatibility_condition",
        "Einstein_coupling_boundary",
        "weak_curvature_or_Poisson_recovery_boundary",
        "failure_or_obstruction_mode",
        "required_Lean_surfaces",
        "required_math_assumptions",
        "required_physics_assumptions",
        "claim_ceiling",
        "forbidden_claims",
        "post_packet_review_target",
    }
    assert required <= set(packet)
    assert packet["scientific_question"] == SCIENTIFIC_QUESTION
    assert packet["required_Lean_surfaces"] == REQUIRED_LEAN_SURFACES
    assert packet["forbidden_claims"] == FORBIDDEN_CLAIMS
    assert packet["post_packet_review_target"] == NEXT_TARGET


def test_qft_gr_conserved_renormalized_source_witness_packet_prepares_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["packet_classification_count"] == 1
    assert packet["witness_packet_prepared"] is True
    assert packet["witness_constructed"] is False
    assert packet["conserved_renormalized_stress_energy_source_exists_claimed"] is False
    assert packet["semiclassical_einstein_equation_derived"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["qft_gr_source_map_closure_claimed"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["scientific_validation_claimed"] is False
    assert packet["master_action_promoted"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["public_submission_authorized"] is False


def test_qft_gr_conserved_renormalized_source_witness_packet_selects_one_next_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == "qft_gr_witness_packet_result_review_only"
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        EXECUTION_TARGET: "deferred",
        "close_qft_gr_seam": "not_authorized",
        "assemble_v01_alpha_release_packet": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }
    assert packet["execution_classification_options"] == EXECUTION_CLASSIFICATIONS
    assert packet["execution_classification_selected"] is None


def test_qft_gr_conserved_renormalized_source_witness_packet_forbidden_claims_false() -> None:
    packet = _json(DEFAULT_OUT)
    assert sorted(packet["forbidden_claim_status"]) == sorted(FORBIDDEN_CLAIMS)
    for claim in FORBIDDEN_CLAIMS:
        assert packet["forbidden_claim_status"][claim] is False


def test_qft_gr_conserved_renormalized_source_witness_packet_deterministic_and_pinned() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_conserved_renormalized_stress_energy_source_witness_packet(
        control_review_path=CONTROL_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert packet == generated
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    refs = [
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        NEXT_TARGET,
        "formal/docs/release/QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_20260525_v0.json",
        "formal/python/tools/qft_gr_conserved_renormalized_stress_energy_source_witness_packet_report.py",
        "formal/python/tests/test_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_gate.py",
    ]
    roadmap = _read(ROADMAP_PATH)
    surfaces = _read(SURFACES_PATH)
    registry = _read(REGISTRY_PATH)
    lean = _read(LEAN_PACKET_PATH)
    frontier = _read(FRONTIER_PATH)
    for ref in refs:
        assert ref in roadmap
    for ref in [PACKET_ID, OUTCOME_ID, PACKET_CLASSIFICATION, NEXT_TARGET]:
        assert ref in surfaces or ref in registry or ref in lean
    for text in [_read(README_PATH), _read(STATE_PATH), frontier]:
        assert NEXT_TARGET in text
        assert "QFT-GR" in text
