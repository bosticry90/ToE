from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)
from formal.python.tools.qft_gr_minimal_working_model_candidate_analysis_result_review_report import (
    DEFAULT_OUT as CANDIDATE_ANALYSIS_RESULT_REVIEW_PATH,
    OUTCOME_ID as CANDIDATE_ANALYSIS_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as CANDIDATE_ANALYSIS_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as CANDIDATE_ANALYSIS_RESULT_REVIEW_ID,
    SCHEMA_ID as CANDIDATE_ANALYSIS_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    SCHEMA_ID,
    TOY_SOURCE_STATUS,
    build_qft_gr_minimal_working_model_conservation_test_packet,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_result_review_report import (
    NEXT_TARGET as CONSERVATION_TEST_ATTEMPT_TARGET,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_conservation_test_packet_report.py"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelConservationTestPacket.lean"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
V01_INDEX_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
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
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for item in payload["workstreams"]:
        if item["workstream_id"] == workstream_id:
            return item
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_minimal_working_model_conservation_test_packet_files_exist() -> None:
    assert CANDIDATE_ANALYSIS_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_minimal_working_model_conservation_test_packet_consumes_review() -> None:
    packet = _json(DEFAULT_OUT)
    review = _json(CANDIDATE_ANALYSIS_RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["accepted"] is True
    assert packet["packet_prepared"] is True
    assert packet["packet_preparation_only"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert (
        packet[
            "consumes_qft_gr_minimal_working_model_candidate_analysis_result_review"
        ]
        == CANDIDATE_ANALYSIS_RESULT_REVIEW_ID
    )
    assert review["schema_id"] == CANDIDATE_ANALYSIS_RESULT_REVIEW_SCHEMA_ID
    assert review["outcome_id"] == CANDIDATE_ANALYSIS_RESULT_REVIEW_OUTCOME
    assert (
        review["result_review_classification"]
        == CANDIDATE_ANALYSIS_RESULT_REVIEW_CLASSIFICATION
    )
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_minimal_working_model_conservation_test_packet_defines_test_protocol() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["toy_source_candidate_status"] == TOY_SOURCE_STATUS
    assert packet["toy_source_candidate_remains_candidate_only"] is True
    assert (
        packet["conservation_sense_being_tested"]["sense_id"]
        == "weak_distributional_covariant_conservation_for_toy_candidate"
    )
    assert packet["conservation_sense_being_tested"]["test_executed"] is False
    assert (
        packet["weak_vs_strong_conservation_scope"]["scope_decision"]
        == "weak_scope_only_for_this_packet"
    )
    assert (
        packet["weak_vs_strong_conservation_scope"]["strong_conservation_tested"]
        is False
    )
    assert (
        packet["test_object_and_test_domain"]["test_object_status"]
        == TOY_SOURCE_STATUS
    )
    assert (
        packet["test_object_and_test_domain"]["test_domain"][
            "source_domain_membership_claimed"
        ]
        is False
    )
    assert len(packet["supplied_assumptions"]) >= 6
    assert set(packet["regularity_assumptions_inherited_from_mr_rows"]) >= {
        "MR-ASSUMP-001-derivative_exchange_regular_boundary",
        "MR-ASSUMP-002-weak_strong_conservation_comparison_scope",
        "MR-ASSUMP-003-distributional_pairing_regular_domain",
        "MR-ASSUMP-004-limit_interchange_regularization_boundary",
    }
    assert set(packet["pass_fail_inconclusive_criteria"]) == {
        "pass",
        "fail",
        "inconclusive",
    }
    assert len(packet["why_passing_does_not_imply_source_admissibility"]) >= 3
    assert (
        len(packet["why_failing_routes_to_countermodel_or_scope_refinement"]) >= 3
    )


def test_minimal_working_model_conservation_test_packet_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "conservation_test_executed",
        "conservation_test_result_claimed",
        "conservation_test_packet_result_reviewed",
        "countermodel_packet_prepared",
        "scope_refinement_packet_prepared",
        "source_admissibility_claimed",
        "stress_energy_source_admissibility_claimed",
        "physical_source_claimed",
        "conservation_claimed",
        "conservation_proved",
        "conservation_proof_object_constructed",
        "conservation_witness_constructed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_seam_closed",
        "qft_gr_source_map_closure_claimed",
        "empirical_validation_claimed",
        "scientific_validation_claimed",
        "master_action_promoted",
        "master_action_promotion_authorized",
        "release_assembly_authorized",
        "release_packet_assembled",
        "public_submission_authorized",
        "publication_authorized",
    ]:
        assert packet[key] is False, key
    assert packet["aggregate_lean_timeout_caveat_preserved"] is True
    assert "full lake build ToeFormal timed out" in packet["validation_caveat"]


def test_minimal_working_model_conservation_test_packet_selects_result_review_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["selected_next_target_count"] == 1
    assert packet["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        "execute_qft_gr_minimal_working_model_conservation_test": (
            "not_authorized_before_packet_result_review"
        ),
        "prepare_qft_gr_minimal_working_model_countermodel_packet": (
            "not_authorized_before_test_result"
        ),
        "prepare_qft_gr_minimal_working_model_scope_refinement_packet": (
            "not_authorized_before_test_result"
        ),
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_minimal_working_model_conservation_test_packet_updates_live_target() -> None:
    registry = _json(REGISTRY_PATH)
    state = registry["current_target_state"]
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == NEXT_TARGET
    assert state["live_next_target"] == CONSERVATION_TEST_ATTEMPT_TARGET
    assert state["active_lane"] == CONSERVATION_TEST_ATTEMPT_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRMinimalWorkingModelConservationTestPacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_RESULT_REVIEW_20260612_v0.json"
    )
    assert state["live_next_target_outcome"] == RESULT_REVIEW_OUTCOME
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSERVATION_TEST_ATTEMPT_TARGET in registry["next_strict_target_coverage"]

    packet_workstream = _workstream(registry, CONSUMED_TARGET)
    assert packet_workstream["status"] == "paused"
    assert packet_workstream["packet_prepared"] == "yes"
    assert packet_workstream["packet_preparation_only"] == "yes"
    assert packet_workstream["selected_next_target"] == NEXT_TARGET
    assert packet_workstream["conservation_test_executed"] == "no"
    assert packet_workstream["source_admissibility_claimed"] == "no"
    assert packet_workstream["conservation_witness_constructed"] == "no"
    assert packet_workstream["qft_gr_closure_claimed"] == "no"

    packet_result_review_workstream = _workstream(registry, NEXT_TARGET)
    assert packet_result_review_workstream["status"] == "paused"
    assert packet_result_review_workstream["selected_next_target"] == (
        CONSERVATION_TEST_ATTEMPT_TARGET
    )
    assert packet_result_review_workstream["packet_result_review_accepted"] == "yes"
    assert (
        packet_result_review_workstream[
            "bounded_conservation_test_attempt_authorized"
        ]
        == "yes"
    )
    assert packet_result_review_workstream["conservation_test_executed"] == "no"
    assert packet_result_review_workstream["source_admissibility_claimed"] == "no"
    assert packet_result_review_workstream["conservation_witness_constructed"] == "no"
    assert packet_result_review_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == CONSERVATION_TEST_ATTEMPT_TARGET
    assert (
        active_workstream["authorized_next_strict_target"]
        == CONSERVATION_TEST_ATTEMPT_TARGET
    )
    assert active_workstream["consumed_target"] == NEXT_TARGET
    assert active_workstream["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert active_workstream["conservation_test_attempt_authorized"] == "yes"
    assert active_workstream["conservation_test_executed"] == "no"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_minimal_working_model_conservation_test_packet_deterministic() -> None:
    packet = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_conservation_test_packet(
        candidate_analysis_result_review_path=CANDIDATE_ANALYSIS_RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-12T00:00:00Z",
    )
    assert packet == generated
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            TOE_FORMAL_PATH,
            V01_INDEX_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            ROADMAP_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            STRICT_MAP_PATH,
            SEAM_REGISTRY_PATH,
            SEAM_INVENTORY_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "weak_distributional_covariant_conservation_for_toy_candidate",
        "weak_scope_only_for_this_packet",
        "MR-ASSUMP-004-limit_interchange_regularization_boundary",
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_minimal_working_model_conservation_test_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_conservation_test_packet_gate.py"
    )
