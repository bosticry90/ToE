from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)
from formal.python.tools.qft_gr_minimal_working_model_candidate_analysis_report import (
    ANALYSIS_CLASSIFICATION,
    ANALYSIS_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    SCHEMA_ID,
    TOY_SOURCE_STATUS,
    build_qft_gr_minimal_working_model_candidate_analysis,
)
from formal.python.tools.qft_gr_minimal_working_model_construction_attempt_report import (
    DEFAULT_OUT as CONSTRUCTION_ATTEMPT_PATH,
)
from formal.python.tools.qft_gr_minimal_working_model_construction_attempt_result_review_report import (
    DEFAULT_OUT as CONSTRUCTION_ATTEMPT_RESULT_REVIEW_PATH,
    OUTCOME_ID as CONSTRUCTION_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as CONSTRUCTION_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as CONSTRUCTION_RESULT_REVIEW_ID,
    SCHEMA_ID as CONSTRUCTION_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_minimal_working_model_candidate_analysis_result_review_report import (
    DEFAULT_OUT as CANDIDATE_ANALYSIS_RESULT_REVIEW_OUT,
    NEXT_TARGET as RESULT_REVIEW_NEXT_TARGET,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
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
    / "qft_gr_minimal_working_model_candidate_analysis_report.py"
)
LEAN_ANALYSIS_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelCandidateAnalysis.lean"
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


def test_minimal_working_model_candidate_analysis_files_exist() -> None:
    assert CONSTRUCTION_ATTEMPT_RESULT_REVIEW_PATH.exists()
    assert CONSTRUCTION_ATTEMPT_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ANALYSIS_PATH.exists()


def test_minimal_working_model_candidate_analysis_consumes_result_review() -> None:
    analysis = _json(DEFAULT_OUT)
    result_review = _json(CONSTRUCTION_ATTEMPT_RESULT_REVIEW_PATH)
    assert analysis["schema_id"] == SCHEMA_ID
    assert analysis["analysis_id"] == ANALYSIS_ID
    assert analysis["accepted"] is True
    assert analysis["analysis_completed"] is True
    assert analysis["outcome_id"] == OUTCOME_ID
    assert analysis["analysis_classification"] == ANALYSIS_CLASSIFICATION
    assert analysis["consumed_target"] == CONSUMED_TARGET
    assert (
        analysis[
            "consumes_qft_gr_minimal_working_model_construction_attempt_result_review"
        ]
        == CONSTRUCTION_RESULT_REVIEW_ID
    )
    assert result_review["schema_id"] == CONSTRUCTION_RESULT_REVIEW_SCHEMA_ID
    assert result_review["outcome_id"] == CONSTRUCTION_RESULT_REVIEW_OUTCOME
    assert (
        result_review["result_review_classification"]
        == CONSTRUCTION_RESULT_REVIEW_CLASSIFICATION
    )
    assert result_review["selected_next_target"] == CONSUMED_TARGET


def test_minimal_working_model_candidate_analysis_records_required_content() -> None:
    analysis = _json(DEFAULT_OUT)
    assert analysis["candidate_analysis_only"] is True
    assert analysis["model_execution_beyond_candidate_analysis"] is False
    assert analysis["toy_source_candidate_status"] == TOY_SOURCE_STATUS
    assert analysis["toy_source_candidate_remains_candidate_only"] is True
    assert analysis["toy_source_promoted_to_admissible_source"] is False
    assert len(analysis["what_model_demonstrates"]) >= 3
    assert len(analysis["what_remains_supplied"]) >= 5
    assert len(analysis["what_fails_or_remains_untested"]) >= 6
    assert set(analysis["candidate_status_map"]) == {
        "domain",
        "regularity",
        "pairing",
        "weak_conservation",
        "source_admissibility",
        "Bianchi_compatibility",
    }
    assert (
        analysis["candidate_status_map"]["domain"]["status"]
        == "supplied_imported_domain_conditions_only"
    )
    assert (
        analysis["candidate_status_map"]["regularity"]["status"]
        == "imported_regularities_recorded_not_reproved"
    )
    assert (
        analysis["candidate_status_map"]["pairing"]["status"]
        == "distributional_pairing_domain_imported_not_validated_for_source"
    )
    assert (
        analysis["candidate_status_map"]["weak_conservation"]["status"]
        == "test_target_recorded_not_proved"
    )
    assert (
        analysis["candidate_status_map"]["source_admissibility"]["status"]
        == TOY_SOURCE_STATUS
    )
    assert (
        analysis["candidate_status_map"]["Bianchi_compatibility"]["status"]
        == "not_tested_not_claimed"
    )


def test_minimal_working_model_candidate_analysis_preserves_nonclaims() -> None:
    analysis = _json(DEFAULT_OUT)
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
        "conservation_test_packet_prepared",
        "countermodel_packet_prepared",
        "scope_refinement_packet_prepared",
    ]:
        assert analysis[key] is False, key
    assert analysis["aggregate_lean_timeout_caveat_preserved"] is True
    assert "full lake build ToeFormal timed out" in analysis["validation_caveat"]


def test_minimal_working_model_candidate_analysis_selects_one_next_target() -> None:
    analysis = _json(DEFAULT_OUT)
    assert analysis["selected_next_target"] == NEXT_TARGET
    assert analysis["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert analysis["selected_next_target_count"] == 1
    assert analysis["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in analysis["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_minimal_working_model_conservation_test_packet": (
            "not_authorized_before_analysis_result_review"
        ),
        "prepare_qft_gr_minimal_working_model_countermodel_packet": (
            "not_authorized_before_analysis_result_review"
        ),
        "prepare_qft_gr_minimal_working_model_scope_refinement_packet": (
            "not_authorized_before_analysis_result_review"
        ),
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
    }


def test_minimal_working_model_candidate_analysis_updates_live_target() -> None:
    registry = _json(REGISTRY_PATH)
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
    assert RESULT_REVIEW_NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CONSERVATION_TEST_PACKET_NEXT_TARGET in registry[
        "next_strict_target_coverage"
    ]
    assert CONSERVATION_TEST_ATTEMPT_TARGET in registry[
        "next_strict_target_coverage"
    ]
    assert CONSERVATION_TEST_ATTEMPT_RESULT_REVIEW_TARGET in registry[
        "next_strict_target_coverage"
    ]

    analysis_workstream = _workstream(registry, CONSUMED_TARGET)
    assert analysis_workstream["status"] == "paused"
    assert analysis_workstream["analysis_completed"] == "yes"
    assert analysis_workstream["selected_next_target"] == NEXT_TARGET
    assert analysis_workstream["toy_source_candidate_status"] == TOY_SOURCE_STATUS
    assert analysis_workstream["source_admissibility_claimed"] == "no"
    assert analysis_workstream["conservation_witness_constructed"] == "no"
    assert analysis_workstream["qft_gr_closure_claimed"] == "no"

    result_review_workstream = _workstream(registry, NEXT_TARGET)
    assert result_review_workstream["status"] == "paused"
    assert result_review_workstream["workstream_id"] == NEXT_TARGET
    assert (
        result_review_workstream["authorized_next_strict_target"]
        == RESULT_REVIEW_NEXT_TARGET
    )
    assert result_review_workstream["consumed_target"] == CONSUMED_TARGET
    assert result_review_workstream["outcome_id"] == RESULT_REVIEW_OUTCOME
    assert result_review_workstream["report"] == str(
        CANDIDATE_ANALYSIS_RESULT_REVIEW_OUT.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert result_review_workstream["result_review_accepted"] == "yes"
    assert result_review_workstream["selected_next_target"] == RESULT_REVIEW_NEXT_TARGET
    assert (
        result_review_workstream["bounded_conservation_test_packet_authorized"]
        == "yes"
    )
    assert result_review_workstream["source_admissibility_claimed"] == "no"
    assert result_review_workstream["conservation_witness_constructed"] == "no"
    assert result_review_workstream["qft_gr_closure_claimed"] == "no"

    conservation_packet_workstream = _workstream(registry, RESULT_REVIEW_NEXT_TARGET)
    assert conservation_packet_workstream["status"] == "paused"
    assert conservation_packet_workstream["report"] == str(
        CONSERVATION_TEST_PACKET_OUT.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert conservation_packet_workstream["packet_prepared"] == "yes"
    assert conservation_packet_workstream["selected_next_target"] == (
        CONSERVATION_TEST_PACKET_NEXT_TARGET
    )
    assert conservation_packet_workstream["conservation_test_executed"] == "no"
    assert conservation_packet_workstream["source_admissibility_claimed"] == "no"
    assert conservation_packet_workstream["conservation_witness_constructed"] == "no"
    assert conservation_packet_workstream["qft_gr_closure_claimed"] == "no"

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


def test_minimal_working_model_candidate_analysis_deterministic_and_pinned() -> None:
    analysis = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_candidate_analysis(
        construction_attempt_result_review_path=CONSTRUCTION_ATTEMPT_RESULT_REVIEW_PATH,
        construction_attempt_path=CONSTRUCTION_ATTEMPT_PATH,
        captured_at_utc="2026-06-12T00:00:00Z",
    )
    assert analysis == generated
    for key, value in analysis["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_ANALYSIS_PATH,
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
        ANALYSIS_ID,
        OUTCOME_ID,
        ANALYSIS_CLASSIFICATION,
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


def test_minimal_working_model_candidate_analysis_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_candidate_analysis_gate.py"
    )
