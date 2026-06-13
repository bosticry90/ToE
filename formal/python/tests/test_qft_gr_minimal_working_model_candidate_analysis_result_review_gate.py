from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_minimal_working_model_candidate_analysis_report import (
    ANALYSIS_CLASSIFICATION,
    ANALYSIS_ID,
    DEFAULT_OUT as CANDIDATE_ANALYSIS_PATH,
    OUTCOME_ID as CANDIDATE_ANALYSIS_OUTCOME,
    SCHEMA_ID as CANDIDATE_ANALYSIS_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_candidate_analysis_result_review_report import (
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    TOY_SOURCE_STATUS,
    build_qft_gr_minimal_working_model_candidate_analysis_result_review,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_report import (
    DEFAULT_OUT as CONSERVATION_TEST_PACKET_OUT,
    NEXT_TARGET as CONSERVATION_TEST_PACKET_NEXT_TARGET,
    OUTCOME_ID as CONSERVATION_TEST_PACKET_OUTCOME,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_packet_result_review_report import (
    NEXT_TARGET as CONSERVATION_TEST_ATTEMPT_TARGET,
    OUTCOME_ID as CONSERVATION_TEST_PACKET_RESULT_REVIEW_OUTCOME,
)
from formal.python.tools.qft_gr_minimal_working_model_conservation_test_attempt_report import (
    NEXT_TARGET as CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET,
    OUTCOME_ID as CONSERVATION_TEST_ATTEMPT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_candidate_analysis_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelCandidateAnalysisResultReview.lean"
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


def test_minimal_working_model_candidate_analysis_result_review_files_exist() -> None:
    assert CANDIDATE_ANALYSIS_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_minimal_working_model_candidate_analysis_result_review_consumes_analysis() -> None:
    review = _json(DEFAULT_OUT)
    analysis = _json(CANDIDATE_ANALYSIS_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["accepted"] is True
    assert review["review_decision"] == "accepted"
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert (
        review["consumes_qft_gr_minimal_working_model_candidate_analysis"]
        == ANALYSIS_ID
    )
    assert analysis["schema_id"] == CANDIDATE_ANALYSIS_SCHEMA_ID
    assert analysis["analysis_id"] == ANALYSIS_ID
    assert analysis["outcome_id"] == CANDIDATE_ANALYSIS_OUTCOME
    assert analysis["analysis_classification"] == ANALYSIS_CLASSIFICATION
    assert analysis["selected_next_target"] == CONSUMED_TARGET


def test_minimal_working_model_candidate_analysis_result_review_confirms_content() -> None:
    review = _json(DEFAULT_OUT)
    assert review["candidate_only_analysis_accepted"] is True
    assert review["bounded_conservation_test_packet_authorized"] is True
    assert review["conservation_test_packet_prepared_by_review"] is False
    assert review["toy_source_candidate_status"] == TOY_SOURCE_STATUS
    assert review["toy_source_candidate_remains_candidate_only"] is True
    assert review["toy_source_promoted_to_admissible_source"] is False
    assert len(review["what_model_demonstrates"]) >= 3
    assert len(review["what_remains_supplied"]) >= 5
    assert len(review["what_fails_or_remains_untested"]) >= 6
    assert review["what_model_demonstrates_recorded"] is True
    assert review["what_remains_supplied_recorded"] is True
    assert review["what_fails_or_remains_untested_recorded"] is True
    assert set(review["candidate_status_map"]) == {
        "domain",
        "regularity",
        "pairing",
        "weak_conservation",
        "source_admissibility",
        "Bianchi_compatibility",
    }
    assert (
        review["candidate_status_map"]["domain"]["status"]
        == "supplied_imported_domain_conditions_only"
    )
    assert (
        review["candidate_status_map"]["regularity"]["status"]
        == "imported_regularities_recorded_not_reproved"
    )
    assert (
        review["candidate_status_map"]["pairing"]["status"]
        == "distributional_pairing_domain_imported_not_validated_for_source"
    )
    assert (
        review["candidate_status_map"]["weak_conservation"]["status"]
        == "test_target_recorded_not_proved"
    )
    assert (
        review["candidate_status_map"]["source_admissibility"]["status"]
        == TOY_SOURCE_STATUS
    )
    assert (
        review["candidate_status_map"]["Bianchi_compatibility"]["status"]
        == "not_tested_not_claimed"
    )


def test_minimal_working_model_candidate_analysis_result_review_preserves_nonclaims() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
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
        assert review[key] is False, key
    assert review["aggregate_lean_timeout_caveat_preserved"] is True
    assert "full lake build ToeFormal timed out" in review["validation_caveat"]


def test_minimal_working_model_candidate_analysis_result_review_selects_one_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["result_review_selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["selected_next_target_count"] == 1
    assert review["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        CONSUMED_TARGET: "completed_consumed_live_target",
        "prepare_qft_gr_minimal_working_model_countermodel_packet": (
            "not_selected_by_this_review"
        ),
        "prepare_qft_gr_minimal_working_model_scope_refinement_packet": (
            "not_selected_by_this_review"
        ),
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_minimal_working_model_candidate_analysis_result_review_updates_live_target() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET)
    state = registry["current_target_state"]
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSERVATION_TEST_ATTEMPT_TARGET
    assert state["live_next_target"] == CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    assert state["active_lane"] == CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRMinimalWorkingModelConservationTestAttempt.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_ATTEMPT_20260612_v0.json"
    )
    assert state["live_next_target_outcome"] == CONSERVATION_TEST_ATTEMPT_OUTCOME
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSERVATION_TEST_PACKET_NEXT_TARGET in registry[
        "next_strict_target_coverage"
    ]
    assert CONSERVATION_TEST_ATTEMPT_TARGET in registry[
        "next_strict_target_coverage"
    ]
    assert CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET in registry[
        "next_strict_target_coverage"
    ]

    review_workstream = _workstream(registry, CONSUMED_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["result_review_accepted"] == "yes"
    assert review_workstream["candidate_analysis_accepted"] == "yes"
    assert review_workstream["selected_next_target"] == NEXT_TARGET
    assert review_workstream["bounded_conservation_test_packet_authorized"] == "yes"
    assert review_workstream["conservation_test_packet_prepared_by_review"] == "no"
    assert review_workstream["source_admissibility_claimed"] == "no"
    assert review_workstream["conservation_witness_constructed"] == "no"
    assert review_workstream["qft_gr_closure_claimed"] == "no"

    packet_workstream = _workstream(registry, NEXT_TARGET)
    assert packet_workstream["status"] == "paused"
    assert packet_workstream["report"] == str(
        CONSERVATION_TEST_PACKET_OUT.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert packet_workstream["packet_prepared"] == "yes"
    assert packet_workstream["selected_next_target"] == (
        CONSERVATION_TEST_PACKET_NEXT_TARGET
    )
    assert packet_workstream["conservation_test_executed"] == "no"
    assert packet_workstream["source_admissibility_claimed"] == "no"
    assert packet_workstream["conservation_witness_constructed"] == "no"
    assert packet_workstream["qft_gr_closure_claimed"] == "no"

    packet_result_review_workstream = _workstream(
        registry, CONSERVATION_TEST_PACKET_NEXT_TARGET
    )
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

    attempt_workstream = _workstream(registry, CONSERVATION_TEST_ATTEMPT_TARGET)
    assert attempt_workstream["status"] == "paused"
    assert attempt_workstream["selected_next_target"] == (
        CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert attempt_workstream["conservation_test_executed"] == "yes"
    assert attempt_workstream["test_inconclusive"] == "yes"
    assert attempt_workstream["source_admissibility_claimed"] == "no"
    assert attempt_workstream["conservation_witness_constructed"] == "no"
    assert attempt_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == (
        CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert (
        active_workstream["authorized_next_strict_target"]
        == CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET
    )
    assert active_workstream["consumed_target"] == CONSERVATION_TEST_ATTEMPT_TARGET
    assert active_workstream["outcome_id"] == CONSERVATION_TEST_ATTEMPT_OUTCOME
    assert active_workstream["conservation_test_attempt_consumed"] == "yes"
    assert active_workstream["conservation_test_executed"] == "yes"
    assert active_workstream["test_inconclusive"] == "yes"
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["conservation_witness_constructed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_minimal_working_model_candidate_analysis_result_review_deterministic() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_candidate_analysis_result_review(
        candidate_analysis_path=CANDIDATE_ANALYSIS_PATH,
        captured_at_utc="2026-06-12T00:00:00Z",
    )
    assert review == generated
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_REVIEW_PATH,
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
        REVIEW_ID,
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "candidate_only_not_source_admissibility",
        "supplied_imported_domain_conditions_only",
        "imported_regularities_recorded_not_reproved",
        "distributional_pairing_domain_imported_not_validated_for_source",
        "test_target_recorded_not_proved",
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_minimal_working_model_candidate_analysis_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_candidate_analysis_result_review_gate.py"
    )
