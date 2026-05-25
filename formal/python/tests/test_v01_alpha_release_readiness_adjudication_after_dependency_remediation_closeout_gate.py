from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result_review_report import (
    DEFAULT_OUT as PACKET_RESULT_REVIEW_PATH,
    OUTCOME_ID as PACKET_RESULT_REVIEW_OUTCOME,
    REVIEW_ID as PACKET_RESULT_REVIEW_ID,
)
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_report import (
    CONSUMED_TARGET,
    CRITICIZABILITY_READINESS_STATUS,
    DEFAULT_OUT,
    EXECUTION_CLASSIFICATION,
    EXECUTION_ID,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    SCHEMA_ID,
    build_release_readiness_adjudication_after_dependency_remediation_closeout,
)
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_report import (
    CRITICIZABILITY_QUESTION,
    EXECUTION_CLASSIFICATIONS,
    REQUIRED_BOUNDARY,
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
    / "v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_report.py"
)
LEAN_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ReleaseReadinessAdjudicationAfterDependencyRemediationCloseout.lean"
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


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_files_exist() -> None:
    assert PACKET_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_EXECUTION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_consumes_review() -> None:
    execution = _json(DEFAULT_OUT)
    review = _json(PACKET_RESULT_REVIEW_PATH)
    assert execution["schema_id"] == SCHEMA_ID
    assert execution["execution_id"] == EXECUTION_ID
    assert execution["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert execution["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert execution["executed"] is True
    assert execution["accepted"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert execution["consumes_criticizability_readiness_packet_result_review"] == (
        PACKET_RESULT_REVIEW_ID
    )
    assert execution["consumes_criticizability_readiness_packet_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_"
        "CLOSEOUT_PACKET_RESULT_REVIEW_20260525_v0.json"
    )
    assert review["outcome_id"] == PACKET_RESULT_REVIEW_OUTCOME
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_executes_one_classification() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["execution_scope"] == (
        "EXECUTE_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_AFTER_"
        "DEPENDENCY_REMEDIATION_CLOSEOUT_ONLY_NO_RELEASE_ASSEMBLY_OR_"
        "SCIENTIFIC_VALIDATION"
    )
    assert execution["execution_classification"] == EXECUTION_CLASSIFICATION
    assert EXECUTION_CLASSIFICATION in EXECUTION_CLASSIFICATIONS
    assert execution["execution_classification_count"] == 1
    assert execution["criticizability_readiness_adjudication_executed"] is True
    assert execution["criticizability_readiness_execution_only"] is True
    assert execution["criticizability_readiness_question"] == CRITICIZABILITY_QUESTION
    assert execution["criticizability_readiness_question_answered"] is True
    assert execution["criticizability_readiness_decision_made"] is True
    assert execution["criticizability_readiness_decision"] == CRITICIZABILITY_READINESS_STATUS
    assert execution["criticizability_readiness_status"] == CRITICIZABILITY_READINESS_STATUS
    assert execution["criticizability_readiness_result_review_required"] is True
    assert execution["required_boundary"] == REQUIRED_BOUNDARY


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_records_eligible_without_release_marking() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["dependency_remediation_closeout_accepted"] is True
    assert execution["dependency_remediation_queue_closed"] is True
    assert execution["all_dependency_tranches_nonblocking"] is True
    assert execution["documented_dependency_nonblocking_tranche_count"] == 6
    assert execution["release_readiness_eligible_for_bounded_criticizability_treatment"] is True
    assert execution["release_readiness_marked"] is False
    assert execution["release_readiness_proceed_authorized"] is False
    assert execution["readiness_marking_authorized"] is False
    assert execution["v01_alpha_marked_ready"] is False


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_preserves_firewalls() -> None:
    execution = _json(DEFAULT_OUT)
    forbidden = execution["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    assert execution["release_assembly_authorized"] is False
    assert execution["release_packet_assembled"] is False
    assert execution["public_submission_authorized"] is False
    assert execution["publication_authorized"] is False
    assert execution["scientific_validation_claimed"] is False
    assert execution["qft_gr_seam_closed"] is False
    assert execution["qft_gr_seam_closure_authorized"] is False
    assert execution["qft_gr_seam_closure_claimed"] is False
    assert execution["qft_gr_source_map_semantic_closure_claimed"] is False
    assert execution["source_map_seam_pillar_master_action_promotion_authorized"] is False
    assert execution["master_action_promotion_authorized"] is False
    assert execution["canonical_toe_claimed"] is False
    assert execution["track2_started"] is False
    assert execution["track2_remains_deferred"] is True
    assert execution["track2_selected_after_this_execution"] is False
    assert execution["track2_scientific_evidence_claimed_from_track1"] is False


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_selects_result_review_only() -> None:
    execution = _json(DEFAULT_OUT)
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == (
        "criticizability_readiness_adjudication_result_review_only"
    )
    assert execution["selection_count"] == 1
    assert execution["next_action_scope"] == (
        "REVIEW_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_RESULT_ONLY_"
        "NO_RELEASE_ASSEMBLY_OR_SCIENTIFIC_VALIDATION"
    )
    assert {row["target"]: row["decision"] for row in execution["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "construct_or_refute_qft_gr_conserved_renormalized_stress_energy_source_witness": "deferred",
        "assemble_v01_alpha_release_packet": "not_authorized",
        "mark_v01_alpha_release_ready": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_deterministic_and_pinned() -> None:
    execution = _json(DEFAULT_OUT)
    generated = build_release_readiness_adjudication_after_dependency_remediation_closeout(
        packet_result_review_path=PACKET_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert execution == generated
    for key, value in execution["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    roadmap_text = _read(ROADMAP_PATH)
    surfaces_text = _read(SURFACES_PATH)
    registry_text = _read(REGISTRY_PATH)
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    lean_text = _read(LEAN_EXECUTION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    refs = [
        EXECUTION_ID,
        "formal/docs/release/V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_CLOSEOUT_20260525_v0.json",
        "formal/python/tools/v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_report.py",
        "formal/python/tests/test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_gate.py",
        OUTCOME_ID,
        EXECUTION_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    for ref in [EXECUTION_ID, OUTCOME_ID, EXECUTION_CLASSIFICATION, NEXT_TARGET]:
        assert ref in surfaces_text or ref in registry_text

    for text in [readme_text, state_text]:
        assert NEXT_TARGET in text
        assert "criticizability-readiness" in text

    assert OUTCOME_ID in lean_text
    assert EXECUTION_CLASSIFICATION in lean_text
    assert (
        "V01ReleaseReadinessAdjudicationAfterDependencyRemediationCloseout"
        in index_text
    )
