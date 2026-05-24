from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_FUTURE_ROUTE,
    TRANCHE_004_STATUS,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_adjudication_report import (
    ASSEMBLE_RELEASE_PACKET_TARGET,
    BLOCKER_MOVEMENT_ADJUDICATION_TARGET,
    REFINED_AUTHORIZATION_ADJUDICATION_TARGET,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_adjudication_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
)
from formal.python.tools.v01_alpha_retained_tranche_004_source_map_closure_registration_packet_report import (
    DEFAULT_OUT,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID,
    SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTION_TARGET,
    build_source_map_closure_registration_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_retained_tranche_004_source_map_closure_registration_packet_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01RetainedTranche004SourceMapClosureRegistrationPacket.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_files_exist() -> None:
    assert DEFAULT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_consumes_result_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(DEFAULT_RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_source_map_closure_adjudication_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_ADJUDICATION_RESULT_REVIEW_20260523_v0.json"
    )
    assert review["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["selected_next_target"] == (
        "prepare_v01_alpha_retained_tranche_004_source_map_closure_registration_packet"
    )


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_prepares_registration_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["packet_scope"] == (
        "PREPARE_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
        "ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["packet_classification_count"] == 1
    assert packet["source_map_closure_registration_packet_prepared"] is True
    assert packet["source_map_closure_registration_packet_preparation_only"] is True
    assert packet["source_map_closure_registration_status_proposed"] == (
        "source_map_closure_registration_proposed_pending_packet_result_review"
    )
    assert packet["source_map_closure_registration_packet_result_review_authorized"] is True
    assert packet["source_map_closure_registration_authorized"] is False
    assert packet["source_map_closure_registration_executed"] is False
    assert packet["source_map_closure_registered"] is False


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_carries_authorization_and_evidence_chain() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["source_map_closure_authorization_accepted_by_review"] is True
    assert (
        packet[
            "source_map_closure_authorization_accepted_for_registration_packet_preparation_only"
        ]
        is True
    )
    assert packet["source_map_closure_authorization_accepted_as_final_closure"] is False
    assert packet["source_map_authorization_adjudication_result_accepted"] is True
    assert packet["witness_chain_construction_accepted"] is True
    assert packet["source_map_witness_chain_construction_accepted"] is True
    assert packet["source_map_closure_requirements_adjudicated"] is True
    assert packet["reviewed_closure_requirement_count"] == 7
    assert packet["accepted_closure_requirement_count"] == 7
    assert packet["reviewed_authorization_requirement_count"] == 7
    assert packet["accepted_authorization_requirement_count"] == 7
    assert packet["reviewed_witness_chain_component_count"] == 7
    assert packet["required_proof_surface_count"] == 7
    assert packet["required_evidence_surface_count"] == 6
    assert packet["registration_criteria_count"] == 4
    assert {row["satisfied_by_input"] for row in packet["registration_criteria"]} == {True}
    assert packet["evidence_chain_count"] == 8
    assert {
        row["chain_id"] for row in packet["evidence_chain"]
    } == {
        "witness_chain_construction_packet",
        "witness_chain_construction_packet_result_review",
        "witness_chain_construction_execution",
        "witness_chain_construction_result_review",
        "source_map_authorization_adjudication_execution",
        "source_map_authorization_adjudication_result_review",
        "source_map_closure_adjudication_execution",
        "source_map_closure_adjudication_result_review",
    }


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_preserves_retained_blocker_and_release_hold() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert packet["selected_remediation_finding_id"] == TRANCHE_004_FINDING_ID
    assert packet["selected_dependency"] == TRANCHE_004_DEPENDENCY
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_004_status"] == TRANCHE_004_STATUS
    assert packet["tranche_005_status"] == TRANCHE_005_STATUS
    assert packet["tranche_006_status"] == TRANCHE_006_STATUS
    assert packet["documented_dependency_nonblocking_tranche_count"] == 5
    assert packet["retained_tranche_004_carry_forward"]["status"] == TRANCHE_004_STATUS
    assert packet["required_future_route_for_tranche_004"] == TRANCHE_004_FUTURE_ROUTE
    assert packet["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert packet["tranche_004_status_moved_by_packet"] is False
    assert packet["tranche_004_status_moved"] is False
    assert packet["tranche_004_retained_blocker_discharged"] is False
    assert packet["release_readiness_decision_status"] == RELEASE_READINESS_DECISION
    assert packet["release_readiness_held"] is True
    assert packet["release_readiness_still_blocked"] is True
    assert packet["release_readiness_proceed_authorized"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["release_packet_assembled"] is False
    assert packet["v01_alpha_marked_ready"] is False


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_no_closure_or_promotion() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["source_map_closure_achieved"] is False
    assert packet["source_map_closure_authorized"] is False
    assert packet["final_source_map_closure_authorized"] is False
    assert packet["source_map_closure_claimed"] is False
    assert packet["source_map_closure_registered"] is False
    assert packet["qft_gr_source_map_semantic_closure_claimed"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["qft_gr_seam_closure_authorized"] is False
    assert packet["qft_gr_seam_closure_claimed"] is False
    assert packet["blocker_movement_authorized"] is False
    assert packet["blocker_movement_registered"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["phase2_authorized"] is False
    assert packet["empirical_validation_authorized"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["publication_authorized"] is False
    assert packet["master_action_promotion_authorized"] is False


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_forbidden_effects_false() -> None:
    packet = _json(DEFAULT_OUT)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_selects_exactly_one_next_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "retained_tranche_004_source_map_closure_registration_packet_"
        "result_review_only"
    )
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "REVIEW_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_"
        "RESULT_ONLY_NO_QFT_GR_SEAM_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_"
        "PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        SOURCE_MAP_CLOSURE_REGISTRATION_EXECUTION_TARGET: "deferred",
        BLOCKER_MOVEMENT_ADJUDICATION_TARGET: "deferred",
        ASSEMBLE_RELEASE_PACKET_TARGET: "not_authorized",
        REFINED_AUTHORIZATION_ADJUDICATION_TARGET: "deferred",
    }


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_source_map_closure_registration_packet(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_source_map_closure_registration_packet(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_RETAINED_TRANCHE_004_SOURCE_MAP_CLOSURE_REGISTRATION_PACKET_20260523_v0.json",
        "formal/python/tools/v01_alpha_retained_tranche_004_source_map_closure_registration_packet_report.py",
        "formal/python/tests/test_v01_alpha_retained_tranche_004_source_map_closure_registration_packet_gate.py",
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        RESULT_REVIEW_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01RetainedTranche004SourceMapClosureRegistrationPacket" in index_text
    assert (
        "v01_alpha_retained_tranche_004_source_map_closure_registration_packet_prepares_registration_only"
        in index_text
    )
