from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_report import (
    DEFAULT_OUT as EXECUTION_PATH,
    EXECUTION_CLASSIFICATION,
    EXECUTION_ID,
    OUTCOME_ID as EXECUTION_OUTCOME,
)
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_result_review_report import (
    CONSUMED_TARGET,
    CRITICIZABILITY_READINESS_REVIEW_DECISION,
    DEFAULT_OUT,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_release_readiness_adjudication_result_review,
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
    / "v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_result_review_report.py"
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01CriticizabilityReadinessAdjudicationResultReview.lean"
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


def test_v01_alpha_criticizability_readiness_result_review_files_exist() -> None:
    assert EXECUTION_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_criticizability_readiness_result_review_consumes_execution() -> None:
    review = _json(DEFAULT_OUT)
    execution = _json(EXECUTION_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_criticizability_readiness_execution"] == EXECUTION_ID
    assert review["consumes_criticizability_readiness_execution_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
        "CLOSEOUT_20260525_v0.json"
    )
    assert execution["outcome_id"] == EXECUTION_OUTCOME
    assert execution["selected_next_target"] == CONSUMED_TARGET


def test_v01_alpha_criticizability_readiness_result_review_accepts_eligibility() -> None:
    review = _json(DEFAULT_OUT)
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["result_classification_count"] == 1
    assert review["consumed_execution_classification"] == EXECUTION_CLASSIFICATION
    assert review["criticizability_readiness_result_reviewed"] is True
    assert review["criticizability_readiness_eligibility_accepted"] is True
    assert review["criticizability_readiness_eligibility_rejected"] is False
    assert review["criticizability_readiness_review_decision"] == (
        CRITICIZABILITY_READINESS_REVIEW_DECISION
    )
    assert review["release_readiness_eligible_for_bounded_criticizability_treatment"] is True
    assert review["release_readiness_marked"] is False
    assert review["release_readiness_proceed_authorized"] is False


def test_v01_alpha_criticizability_readiness_result_review_authorizes_witness_packet_only() -> None:
    review = _json(DEFAULT_OUT)
    assert review["qft_gr_witness_packet_preparation_authorized"] is True
    assert review["qft_gr_witness_packet_prepared"] is False
    assert review["qft_gr_witness_execution_authorized"] is False
    assert review["qft_gr_witness_executed"] is False
    assert review["track2_selected_after_result_review"] is True
    assert review["track2_selection_kind"] == "qft_gr_witness_packet_preparation_only"
    assert review["track2_started"] is False
    assert review["track2_science_lane_execution_started"] is False
    assert review["track2_scientific_evidence_claimed_from_track1"] is False


def test_v01_alpha_criticizability_readiness_result_review_preserves_firewalls() -> None:
    review = _json(DEFAULT_OUT)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert review["release_assembly_authorized"] is False
    assert review["release_packet_assembled"] is False
    assert review["readiness_marking_authorized"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["public_submission_authorized"] is False
    assert review["publication_authorized"] is False
    assert review["scientific_validation_claimed"] is False
    assert review["qft_gr_seam_closed"] is False
    assert review["qft_gr_seam_closure_authorized"] is False
    assert review["qft_gr_seam_closure_claimed"] is False
    assert review["qft_gr_source_map_semantic_closure_claimed"] is False
    assert review["source_map_seam_pillar_master_action_promotion_authorized"] is False
    assert review["master_action_promotion_authorized"] is False
    assert review["canonical_toe_claimed"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["proof_debt_reduced"] is False
    assert review["phase2_authorized"] is False
    assert review["empirical_validation_authorized"] is False


def test_v01_alpha_criticizability_readiness_result_review_selects_one_next_target() -> None:
    review = _json(DEFAULT_OUT)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == "qft_gr_witness_packet_preparation_only"
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
        "PACKET_ONLY_NO_TRACK2_EXECUTION_RELEASE_ASSEMBLY_OR_SCIENTIFIC_"
        "VALIDATION"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_qft_gr_conserved_renormalized_stress_energy_source_witness": (
            "not_authorized"
        ),
        "assemble_v01_alpha_release_packet": "not_authorized",
        "authorize_public_submission": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
    }


def test_v01_alpha_criticizability_readiness_result_review_deterministic_and_pinned() -> None:
    review = _json(DEFAULT_OUT)
    generated = build_release_readiness_adjudication_result_review(
        execution_path=EXECUTION_PATH,
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
        "formal/docs/release/V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_REVIEW_20260525_v0.json",
        "formal/python/tools/v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_result_review_report.py",
        "formal/python/tests/test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_result_review_gate.py",
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
    assert NEXT_TARGET in lean_text
    assert "V01CriticizabilityReadinessAdjudicationResultReview" in index_text
