from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_result_review_report import (
    DEFAULT_OUT as CLOSEOUT_RESULT_REVIEW_PATH,
    OUTCOME_ID as CLOSEOUT_RESULT_REVIEW_OUTCOME,
    REVIEW_ID as CLOSEOUT_RESULT_REVIEW_ID,
)
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_report import (
    CONSUMED_TARGET,
    CRITICIZABILITY_QUESTION,
    CRITICIZABILITY_READINESS_PACKET_STATUS,
    DEFAULT_OUT,
    EXECUTION_CLASSIFICATIONS,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REQUIRED_BOUNDARY,
    SCHEMA_ID,
    build_release_readiness_adjudication_packet,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_report import (
    REGISTERED_TRANCHE_004_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / (
        "v01_alpha_release_readiness_adjudication_after_dependency_"
        "remediation_closeout_packet_report.py"
    )
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ReleaseReadinessAdjudicationAfterDependencyRemediationCloseoutPacket.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_files_exist() -> None:
    assert CLOSEOUT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_consumes_closeout_result_review() -> None:
    packet = _json(DEFAULT_OUT)
    closeout_review = _json(CLOSEOUT_RESULT_REVIEW_PATH)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["consumes_dependency_remediation_closeout_result_review"] == (
        CLOSEOUT_RESULT_REVIEW_ID
    )
    assert packet["consumes_dependency_remediation_closeout_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
        "MOVEMENT_RESULT_REVIEW_20260523_v0.json"
    )
    assert closeout_review["outcome_id"] == CLOSEOUT_RESULT_REVIEW_OUTCOME
    assert closeout_review["selected_next_target"] == CONSUMED_TARGET


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_prepares_criticizability_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["packet_classification_count"] == 1
    assert packet["criticizability_readiness_adjudication_packet_prepared"] is True
    assert packet["release_readiness_adjudication_packet_prepared"] is True
    assert packet["criticizability_readiness_adjudication_prepared"] is True
    assert packet["criticizability_readiness_question"] == CRITICIZABILITY_QUESTION
    assert packet["criticizability_readiness_question_prepared"] is True
    assert packet["criticizability_readiness_question_answered"] is False
    assert packet["criticizability_readiness_decision_made"] is False
    assert packet["criticizability_readiness_status"] == CRITICIZABILITY_READINESS_PACKET_STATUS
    assert packet["criticizability_readiness_result_review_required"] is True
    assert packet["required_boundary"] == REQUIRED_BOUNDARY
    assert packet["criticizability_readiness_firewall_defined"] is True
    assert packet["preparation_criteria_count"] == 4


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_confirms_dependency_closeout() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["dependency_remediation_closeout_accepted"] is True
    assert packet["dependency_remediation_queue_closed"] is True
    assert packet["dependency_remediation_queue_exhausted"] is True
    assert packet["all_dependency_tranches_nonblocking"] is True
    assert packet["documented_dependency_nonblocking_tranche_count"] == 6
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_004_status"] == REGISTERED_TRANCHE_004_STATUS
    assert packet["tranche_004_status_exact"] == REGISTERED_TRANCHE_004_STATUS
    assert packet["tranche_004_cleared_for_release_readiness"] is False
    assert packet["tranche_005_status"] == TRANCHE_005_STATUS
    assert packet["tranche_006_status"] == TRANCHE_006_STATUS
    assert packet["unresolved_dependency_remediation_tranche_count"] == 0
    assert packet["source_map_closure_registered"] is True
    assert packet["source_map_closure_achieved"] is True
    assert packet["source_map_closure_external_truth_claimed"] is False


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_preserves_firewalls() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["release_readiness_adjudication_preparation_authorized"] is True
    assert packet["release_readiness_adjudication_prepared"] is True
    assert packet["release_readiness_eligible_for_adjudication"] is False
    assert packet["release_readiness_held"] is True
    assert packet["release_readiness_still_blocked"] is True
    assert packet["release_readiness_proceed_authorized"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["release_packet_assembled"] is False
    assert packet["readiness_marking_authorized"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["public_submission_authorized"] is False
    assert packet["publication_authorized"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["qft_gr_seam_closure_authorized"] is False
    assert packet["qft_gr_seam_closure_claimed"] is False
    assert packet["qft_gr_source_map_semantic_closure_claimed"] is False
    assert packet["semiclassical_einstein_equation_derivation_claimed"] is False
    assert packet["scientific_validation_claimed"] is False
    assert packet["master_action_promotion_authorized"] is False
    assert packet["canonical_toe_claimed"] is False


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_defers_track2_without_science_claim() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["track2_may_be_prepared_after_result_review"] is True
    assert packet["track2_qft_gr_witness_target"] == (
        "construct_or_refute_qft_gr_conserved_renormalized_stress_"
        "energy_source_witness"
    )
    assert packet["track2_qft_gr_witness_target_deferred_until_result_review"] is True
    assert packet["track2_control_clearance_only"] is True
    assert packet["track2_scientific_evidence_claimed_from_track1"] is False


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_selects_exactly_one_next_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "criticizability_readiness_packet_result_review_only"
    )
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "REVIEW_V01_ALPHA_CRITICIZABILITY_READINESS_ADJUDICATION_PACKET_"
        "RESULT_ONLY_NO_RELEASE_ASSEMBLY_OR_SCIENTIFIC_VALIDATION"
    )
    assert packet["execution_classification_options"] == EXECUTION_CLASSIFICATIONS
    assert packet["execution_classification_option_count"] == 3
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "execute_v01_alpha_criticizability_readiness_adjudication_after_dependency_remediation_closeout": "deferred",
        "construct_or_refute_qft_gr_conserved_renormalized_stress_energy_source_witness": "deferred_until_result_review",
        "assemble_v01_alpha_release_packet": "not_authorized",
        "mark_v01_alpha_release_ready": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
    }


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_forbidden_effects_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False

    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_release_readiness_adjudication_packet(
        closeout_result_review_path=CLOSEOUT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_release_readiness_adjudication_packet(
        closeout_result_review_path=CLOSEOUT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    surfaces_text = _read(SURFACES_PATH)
    registry_text = _read(REGISTRY_PATH)
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_REMEDIATION_CLOSEOUT_PACKET_20260525_v0.json",
        "formal/python/tools/v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_report.py",
        "formal/python/tests/test_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_gate.py",
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        CRITICIZABILITY_QUESTION,
        REQUIRED_BOUNDARY,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    for ref in [
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        CRITICIZABILITY_QUESTION,
        REQUIRED_BOUNDARY,
        NEXT_TARGET,
    ]:
        assert ref in surfaces_text or ref in registry_text

    for text in [readme_text, state_text]:
        assert NEXT_TARGET in text
        assert "criticizability-readiness" in text

    assert OUTCOME_ID in lean_text
    assert PACKET_CLASSIFICATION in lean_text
    assert "V01ReleaseReadinessAdjudicationAfterDependencyRemediationCloseoutPacket" in index_text
    assert (
        "v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_prepares_criticizability_question_only"
        in lean_text
    )
