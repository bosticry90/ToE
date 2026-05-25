from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_report import (
    CRITICIZABILITY_QUESTION,
    DEFAULT_OUT as PACKET_PATH,
    EXECUTION_CLASSIFICATIONS,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REQUIRED_BOUNDARY,
)
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result_review_report import (
    CONSUMED_TARGET,
    CRITICIZABILITY_READINESS_PACKET_RESULT_REVIEW_STATUS,
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_release_readiness_adjudication_packet_result_review,
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
    / (
        "v01_alpha_release_readiness_adjudication_after_dependency_"
        "remediation_closeout_packet_result_review_report.py"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / (
        "V01ReleaseReadinessAdjudicationAfterDependencyRemediationCloseout"
        "PacketResultReview.lean"
    )
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
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


def test_v01_alpha_release_readiness_adjudication_packet_result_review_files_exist() -> None:
    assert PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_release_readiness_adjudication_packet_result_review_consumes_packet() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(PACKET_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_criticizability_readiness_packet"] == PACKET_ID
    assert review["consumes_criticizability_readiness_packet_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
        "CLOSEOUT_PACKET_20260525_v0.json"
    )
    assert packet["outcome_id"] == PACKET_OUTCOME
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["selected_next_target"] == CONSUMED_TARGET


def test_v01_alpha_release_readiness_adjudication_packet_result_review_accepts_criticizability_only_packet() -> None:
    review = _json(DEFAULT_OUT)
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["result_classification_count"] == 1
    assert review["criticizability_readiness_packet_result_reviewed"] is True
    assert review["criticizability_readiness_packet_accepted"] is True
    assert review["criticizability_readiness_packet_prepared_only"] is True
    assert review["criticizability_readiness_adjudication_packet_prepared"] is True
    assert review["criticizability_readiness_adjudication_execution_authorized"] is True
    assert review["criticizability_readiness_adjudication_executed"] is False
    assert review["criticizability_readiness_decision_made"] is False
    assert review["criticizability_readiness_question"] == CRITICIZABILITY_QUESTION
    assert review["criticizability_readiness_question_answered"] is False
    assert review["criticizability_readiness_status"] == (
        CRITICIZABILITY_READINESS_PACKET_RESULT_REVIEW_STATUS
    )
    assert review["required_boundary"] == REQUIRED_BOUNDARY


def test_v01_alpha_release_readiness_adjudication_packet_result_review_preserves_boundaries() -> None:
    review = _json(DEFAULT_OUT)
    assert review["dependency_remediation_closeout_accepted"] is True
    assert review["dependency_remediation_queue_closed"] is True
    assert review["all_dependency_tranches_nonblocking"] is True
    assert review["documented_dependency_nonblocking_tranche_count"] == 6
    assert review["release_assembly_authorized"] is False
    assert review["release_packet_assembled"] is False
    assert review["readiness_marking_authorized"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["public_submission_authorized"] is False
    assert review["publication_authorized"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["qft_gr_seam_closure_authorized"] is False
    assert review["qft_gr_seam_closure_claimed"] is False
    assert review["qft_gr_source_map_semantic_closure_claimed"] is False
    assert review["source_map_seam_pillar_master_action_promotion_authorized"] is False
    assert review["scientific_validation_claimed"] is False
    assert review["master_action_promotion_authorized"] is False
    assert review["canonical_toe_claimed"] is False


def test_v01_alpha_release_readiness_adjudication_packet_result_review_selects_execution_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "criticizability_readiness_adjudication_execution_only"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "EXECUTE_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_ONLY_NO_"
        "RELEASE_ASSEMBLY_OR_SCIENTIFIC_VALIDATION"
    )
    assert review["execution_classification_options"] == EXECUTION_CLASSIFICATIONS
    assert review["execution_classification_option_count"] == 3
    assert review["execution_classification_selected"] is None
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "construct_or_refute_qft_gr_conserved_renormalized_stress_energy_source_witness": "deferred",
        "assemble_v01_alpha_release_packet": "not_authorized",
        "mark_v01_alpha_release_ready": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
    }
    assert review["track2_remains_deferred"] is True
    assert review["track2_selected_after_this_review"] is False
    assert review["track2_scientific_evidence_claimed_from_track1"] is False


def test_v01_alpha_release_readiness_adjudication_packet_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_release_readiness_adjudication_packet_result_review(
        packet_path=PACKET_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert review == generated
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    roadmap_text = _read(ROADMAP_PATH)
    surfaces_text = _read(SURFACES_PATH)
    registry_text = _read(REGISTRY_PATH)
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    lean_text = _read(LEAN_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_CLOSEOUT_PACKET_RESULT_REVIEW_20260525_v0.json",
        "formal/python/tools/v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result_review_report.py",
        "formal/python/tests/test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result_review_gate.py",
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    for ref in [REVIEW_ID, OUTCOME_ID, RESULT_REVIEW_CLASSIFICATION, NEXT_TARGET]:
        assert ref in surfaces_text or ref in registry_text

    for text in [readme_text, state_text]:
        assert NEXT_TARGET in text
        assert "criticizability-readiness" in text

    assert OUTCOME_ID in lean_text
    assert RESULT_REVIEW_CLASSIFICATION in lean_text
    assert (
        "V01ReleaseReadinessAdjudicationAfterDependencyRemediationCloseoutPacketResultReview"
        in index_text
    )
