from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_report import (
    CLOSEOUT_CLASSIFICATION,
    DEFAULT_OUT,
    DEFAULT_RESULT_REVIEW_PATH,
    FORBIDDEN_EFFECTS,
    NEXT_TARGET,
    OUTCOME_ID,
    PACKET_ID,
    RELEASE_READINESS_STATUS,
    SCHEMA_ID,
    build_closeout_packet,
)
from formal.python.tools.v01_alpha_retained_tranche_004_blocker_movement_registration_after_source_map_closure_result_review_report import (
    REGISTERED_TRANCHE_004_STATUS,
    REVIEW_ID as RESULT_REVIEW_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_FINDING_ID,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationCloseoutAfterTranche004Movement.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_files_exist() -> None:
    assert DEFAULT_RESULT_REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_consumes_tranche_004_review() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert packet["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert packet["accepted"] is True
    assert packet["prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert (
        packet["consumes_tranche_004_movement_registration_result_review"]
        == RESULT_REVIEW_ID
    )
    assert packet["consumes_tranche_004_movement_registration_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_RETAINED_TRANCHE_004_BLOCKER_MOVEMENT_REGISTRATION_"
        "AFTER_SOURCE_MAP_CLOSURE_RESULT_REVIEW_20260523_v0.json"
    )


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_records_closeout_only() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["packet_scope"] == (
        "PREPARE_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
        "MOVEMENT_ONLY_NO_RELEASE_READINESS_OR_QFT_GR_SEAM_CLOSURE"
    )
    assert packet["dependency_remediation_closeout_classification"] == (
        CLOSEOUT_CLASSIFICATION
    )
    assert packet["dependency_remediation_closeout_classification_count"] == 1
    assert packet["dependency_remediation_closeout_packet_prepared"] is True
    assert packet["dependency_remediation_closeout_prepared"] is True
    assert packet["dependency_remediation_closeout_result_review_required"] is True
    assert packet["dependency_remediation_closeout_status"] == (
        "dependency_remediation_closeout_prepared_pending_result_review"
    )
    assert packet["closeout_criteria_count"] == 4


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_confirms_all_tranches_nonblocking() -> None:
    packet = _json(DEFAULT_OUT)
    documented = packet["documented_dependency_nonblocking_tranches"]
    assert packet["dependency_remediation_queue_exhausted"] is True
    assert packet["dependency_remediation_blocker_queue_exhausted"] is True
    assert packet["simple_dependency_remediation_queue_exhausted"] is True
    assert packet["all_dependency_tranches_nonblocking"] is True
    assert packet["documented_dependency_nonblocking_tranche_count"] == 6
    assert [row["finding_id"] for row in documented] == [
        "V01-ALPHA-DEP-REM-001",
        "V01-ALPHA-DEP-REM-002",
        "V01-ALPHA-DEP-REM-003",
        TRANCHE_004_FINDING_ID,
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    assert packet["tranche_001_status"] == TRANCHE_001_STATUS
    assert packet["tranche_002_status"] == TRANCHE_002_STATUS
    assert packet["tranche_003_status"] == TRANCHE_003_STATUS
    assert packet["tranche_004_status"] == REGISTERED_TRANCHE_004_STATUS
    assert packet["tranche_004_status_exact"] == "documented_source_map_closed_nonblocking"
    assert packet["tranche_004_formal_movement_accepted"] is True
    assert packet["tranche_004_retained_blocker_discharged"] is True
    assert packet["tranche_004_cleared_for_release_readiness"] is False
    assert packet["tranche_005_status"] == TRANCHE_005_STATUS
    assert packet["tranche_006_status"] == TRANCHE_006_STATUS
    assert packet["unresolved_dependency_remediation_tranches"] == []
    assert packet["unresolved_dependency_remediation_tranche_count"] == 0


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_preserves_source_map_evidence_without_seam_closure() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["registered_source_map_closure_accepted_by_review"] is True
    assert packet["source_map_closure_registered"] is True
    assert packet["final_source_map_closure_registered"] is True
    assert packet["source_map_closure_achieved"] is True
    assert packet["source_map_closure_claimed"] is False
    assert packet["source_map_closure_external_truth_claimed"] is False
    assert packet["qft_gr_source_map_semantic_closure_claimed"] is False
    assert packet["qft_gr_seam_closed"] is False
    assert packet["qft_gr_seam_closure_authorized"] is False
    assert packet["qft_gr_seam_closure_claimed"] is False


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_does_not_mark_release_or_discharge_debt() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["release_readiness_decision_status"] == RELEASE_READINESS_STATUS
    assert packet["release_readiness_held"] is True
    assert packet["release_readiness_still_blocked"] is True
    assert packet["release_readiness_proceed_authorized"] is False
    assert packet["release_readiness_adjudication_prepared"] is False
    assert packet["release_assembly_authorized"] is False
    assert packet["release_packet_assembled"] is False
    assert packet["readiness_marking_authorized"] is False
    assert packet["v01_alpha_marked_ready"] is False
    assert packet["lean_theorem_debt_discharged"] is False
    assert packet["axiom_spec_backed_debt_reduced"] is False
    assert packet["proof_debt_reduced"] is False
    assert packet["retained_assumptions_discharged"] is False
    assert packet["theorem_discharge_authorized"] is False
    assert packet["phase2_authorized"] is False
    assert packet["empirical_validation_authorized"] is False
    assert packet["empirical_validation_claimed"] is False
    assert packet["publication_authorized"] is False
    assert packet["master_action_promotion_authorized"] is False


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_forbidden_effects_false() -> None:
    packet = _json(DEFAULT_OUT)
    forbidden = packet["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_EFFECTS)
    for key in FORBIDDEN_EFFECTS:
        assert forbidden[key] is False


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_selects_exactly_one_next_target() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == (
        "dependency_remediation_closeout_after_tranche_004_movement_result_review_only"
    )
    assert packet["selection_count"] == 1
    assert packet["next_action_scope"] == (
        "REVIEW_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
        "MOVEMENT_RESULT_ONLY_NO_RELEASE_READINESS_OR_QFT_GR_SEAM_CLOSURE"
    )
    assert {row["target"]: row["decision"] for row in packet["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout": "deferred",
        "close_qft_gr_seam": "not_authorized",
        "assemble_v01_alpha_release_packet": "not_authorized",
        "mark_v01_alpha_release_ready": "not_authorized",
    }


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_acceptance_and_determinism() -> None:
    packet = _json(DEFAULT_OUT)
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_closeout_packet(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_closeout_packet(
        result_review_path=DEFAULT_RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert packet == generated_1


def test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    refs = [
        PACKET_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_MOVEMENT_20260523_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_gate.py",
        OUTCOME_ID,
        CLOSEOUT_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_PACKET_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationCloseoutAfterTranche004Movement" in index_text
    assert (
        "v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_records_all_tranches_nonblocking"
        in index_text
    )
