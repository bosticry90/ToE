from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)
from formal.python.tools.qft_gr_minimal_working_model_construction_attempt_report import (
    ALLOWED_RESULT_CLASSIFICATIONS,
    ATTEMPT_ID,
    CONSTRUCTION_STATUS,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DEFAULT_PACKET_RESULT_REVIEW_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    RESULT_CLASSIFICATION,
    SCHEMA_ID,
    TOY_SOURCE_STATUS,
    build_qft_gr_minimal_working_model_construction_attempt,
)
from formal.python.tools.qft_gr_minimal_working_model_construction_attempt_result_review_report import (
    DEFAULT_OUT as RESULT_REVIEW_OUT,
    NEXT_TARGET as RESULT_REVIEW_NEXT_TARGET,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
)
from formal.python.tools.qft_gr_minimal_working_model_candidate_analysis_report import (
    DEFAULT_OUT as CANDIDATE_ANALYSIS_OUT,
    NEXT_TARGET as CANDIDATE_ANALYSIS_NEXT_TARGET,
    OUTCOME_ID as CANDIDATE_ANALYSIS_OUTCOME,
)
from formal.python.tools.qft_gr_minimal_working_model_demonstration_packet_result_review_report import (
    OUTCOME_ID as PACKET_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as PACKET_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as PACKET_RESULT_REVIEW_ID,
    SCHEMA_ID as PACKET_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_minimal_working_model_construction_attempt_report.py"
)
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMinimalWorkingModelConstructionAttempt.lean"
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


def test_minimal_working_model_construction_attempt_files_exist() -> None:
    assert DEFAULT_PACKET_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()


def test_minimal_working_model_construction_attempt_consumes_result_review() -> None:
    attempt = _json(DEFAULT_OUT)
    review = _json(DEFAULT_PACKET_RESULT_REVIEW_PATH)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["executed"] is True
    assert attempt["accepted"] is True
    assert attempt["outcome_id"] == OUTCOME_ID
    assert attempt["result_classification"] == RESULT_CLASSIFICATION
    assert attempt["consumed_target"] == CONSUMED_TARGET
    assert (
        attempt["consumes_qft_gr_minimal_working_model_demonstration_packet_result_review"]
        == PACKET_RESULT_REVIEW_ID
    )
    assert review["schema_id"] == PACKET_RESULT_REVIEW_SCHEMA_ID
    assert review["outcome_id"] == PACKET_RESULT_REVIEW_OUTCOME
    assert review["result_review_classification"] == PACKET_RESULT_REVIEW_CLASSIFICATION
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_minimal_working_model_construction_attempt_constructs_candidate_only() -> None:
    attempt = _json(DEFAULT_OUT)
    model = attempt["bounded_minimal_model_attempt"]
    assert attempt["construction_status"] == CONSTRUCTION_STATUS
    assert attempt["construction_attempt_executed"] is True
    assert attempt["construction_attempt_pending_result_review"] is True
    assert attempt["bounded_model_construction_attempt_only"] is True
    assert model["model_class"] == "free scalar-field stress-energy-like candidate"
    assert model["background"]["backreaction"] == "excluded"
    assert model["stress_energy_like_candidate"]["status"] == TOY_SOURCE_STATUS
    assert model["stress_energy_like_candidate"]["source_admissibility_claimed"] is False
    assert (
        model["weak_conservation_test_target"]["status"]
        == "test_target_recorded_not_proved"
    )
    assert model["weak_conservation_test_target"]["conservation_claimed"] is False
    assert (
        model["weak_conservation_test_target"]["conservation_witness_constructed"]
        is False
    )


def test_minimal_working_model_construction_attempt_preserves_nonclaims() -> None:
    attempt = _json(DEFAULT_OUT)
    for key in [
        "model_execution_beyond_construction_attempt",
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
        assert attempt[key] is False, key
    assert attempt["aggregate_lean_timeout_caveat_preserved"] is True
    assert "full lake build ToeFormal timed out" in attempt["validation_caveat"]


def test_minimal_working_model_construction_attempt_selects_one_next_target() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["result_classification"] in ALLOWED_RESULT_CLASSIFICATIONS
    assert attempt["result_classification_count"] == 1
    assert sum(1 for row in attempt["classification_rows"] if row["selected"]) == 1
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert attempt["selected_next_target_count"] == 1
    assert attempt["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in attempt["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "claim_qft_gr_source_admissibility": "not_authorized",
        "prove_qft_gr_conservation": "not_authorized",
        "construct_qft_gr_conservation_witness": "not_authorized",
        "claim_qft_gr_bianchi_compatibility": "not_authorized",
        "derive_semiclassical_einstein_equation": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_empirical_validation_or_public_submission": "not_authorized",
    }


def test_minimal_working_model_construction_attempt_updates_live_target() -> None:
    registry = _json(REGISTRY_PATH)
    state = registry["current_target_state"]
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == RESULT_REVIEW_NEXT_TARGET
    assert state["live_next_target"] == CANDIDATE_ANALYSIS_NEXT_TARGET
    assert state["active_lane"] == CANDIDATE_ANALYSIS_NEXT_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRMinimalWorkingModelCandidateAnalysis.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_MINIMAL_WORKING_MODEL_CANDIDATE_ANALYSIS_20260612_v0.json"
    )
    assert state["live_next_target_outcome"] == CANDIDATE_ANALYSIS_OUTCOME
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert RESULT_REVIEW_NEXT_TARGET in registry["next_strict_target_coverage"]
    assert CANDIDATE_ANALYSIS_NEXT_TARGET in registry["next_strict_target_coverage"]

    attempt_workstream = _workstream(registry, CONSUMED_TARGET)
    assert attempt_workstream["status"] == "paused"
    assert attempt_workstream["bounded_minimal_model_attempt_constructed"] == "yes"
    assert attempt_workstream["toy_source_candidate_status"] == TOY_SOURCE_STATUS
    assert attempt_workstream["selected_next_target"] == NEXT_TARGET
    assert attempt_workstream["source_admissibility_claimed"] == "no"
    assert attempt_workstream["conservation_witness_constructed"] == "no"
    assert attempt_workstream["qft_gr_closure_claimed"] == "no"

    review_workstream = _workstream(registry, NEXT_TARGET)
    assert review_workstream["status"] == "paused"
    assert review_workstream["report"] == str(
        RESULT_REVIEW_OUT.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert review_workstream["selected_next_target"] == RESULT_REVIEW_NEXT_TARGET
    assert review_workstream["model_analysis_only_authorized"] == "yes"
    assert review_workstream["model_analysis_executed_by_review"] == "no"
    assert review_workstream["source_admissibility_claimed"] == "no"
    assert review_workstream["conservation_witness_constructed"] == "no"
    assert review_workstream["qft_gr_closure_claimed"] == "no"

    analysis_workstream = _workstream(registry, RESULT_REVIEW_NEXT_TARGET)
    assert analysis_workstream["status"] == "paused"
    assert analysis_workstream["report"] == str(
        CANDIDATE_ANALYSIS_OUT.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert analysis_workstream["analysis_completed"] == "yes"
    assert analysis_workstream["selected_next_target"] == CANDIDATE_ANALYSIS_NEXT_TARGET
    assert analysis_workstream["source_admissibility_claimed"] == "no"
    assert analysis_workstream["conservation_witness_constructed"] == "no"
    assert analysis_workstream["qft_gr_closure_claimed"] == "no"

    active_workstream = active[0]
    assert active_workstream["workstream_id"] == CANDIDATE_ANALYSIS_NEXT_TARGET
    assert active_workstream["authorized_next_strict_target"] == (
        CANDIDATE_ANALYSIS_NEXT_TARGET
    )
    assert active_workstream["consumed_target"] == RESULT_REVIEW_NEXT_TARGET
    assert active_workstream["outcome_id"] == CANDIDATE_ANALYSIS_OUTCOME
    assert active_workstream["source_admissibility_claimed"] == "no"
    assert active_workstream["qft_gr_closure_claimed"] == "no"


def test_minimal_working_model_construction_attempt_deterministic_and_pinned() -> None:
    attempt = _json(DEFAULT_OUT)
    generated = build_qft_gr_minimal_working_model_construction_attempt(
        packet_result_review_path=DEFAULT_PACKET_RESULT_REVIEW_PATH,
        captured_at_utc="2026-06-11T00:00:00Z",
    )
    assert attempt == generated
    for key, value in attempt["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            LEAN_ATTEMPT_PATH,
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
        ATTEMPT_ID,
        OUTCOME_ID,
        RESULT_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        "candidate_only_not_source_admissibility",
        "no source admissibility",
        "no conservation witness",
        "no Bianchi compatibility",
        "no semiclassical Einstein equation",
        "no QFT-GR closure",
        "no empirical validation",
        "no public submission",
    ]:
        assert token in joined


def test_minimal_working_model_construction_attempt_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_minimal_working_model_construction_attempt_gate.py"
    )
