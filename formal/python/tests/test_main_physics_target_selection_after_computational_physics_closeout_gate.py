from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.main_physics_target_selection_after_computational_physics_closeout_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXPECTED_SELECTED_TARGET,
    OUTCOME_ID,
    build_selection,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
CLOSEOUT_REVIEW_PATH = (
    RELEASE_DIR / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0.json"
)
SELECTION_PATH = (
    RELEASE_DIR / "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_20260515_v0.json"
)
LOOP_REGISTRY_PATH = RELEASE_DIR / "LOOP_CONTROL_REGISTRY_v0.json"
V01_REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_20260513_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "main_physics_target_selection_after_computational_physics_closeout_report.py"
)
ROADMAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

FORBIDDEN_TRUE_KEYS = [
    "computational_physics_execution_surface_opened",
    "theory_validation_authorized",
    "empirical_validation_authorized",
    "referent_comparison_execution_authorized",
    "robustness_scan_execution_authorized",
    "prediction_execution_authorized",
    "falsifier_execution_authorized",
    "theorem_discharge_authorized",
    "blocker_movement_authorized",
    "lane_reopen_authorized",
    "seam_closure_authorized",
    "phase2_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "release_packet_assembly_authorized",
    "public_release_completion_authorized",
]

PROHIBITED_PHRASES = [
    "computational physics execution opened",
    "theory validation complete",
    "empirical validation complete",
    "referent comparison executed",
    "robustness scan executed",
    "prediction confirmed",
    "falsifier executed",
    "falsifier passed",
    "Phase 2 authorized",
    "seam closure authorized",
    "theorem discharged by computation",
    "master action promoted",
    "release packet assembled",
    "public release complete",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_main_physics_target_selection_after_closeout_files_exist() -> None:
    assert CLOSEOUT_REVIEW_PATH.exists()
    assert SELECTION_PATH.exists()
    assert LOOP_REGISTRY_PATH.exists()
    assert V01_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_main_physics_target_selection_after_closeout_consumes_closed_stack() -> None:
    selection = _json(SELECTION_PATH)
    assert (
        selection["schema_id"]
        == "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_20260515_v0"
    )
    assert selection["selection_id"] == "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_v0"
    assert selection["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert selection["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert selection["accepted"] is True
    assert selection["outcome_id"] == OUTCOME_ID
    assert (
        selection["consumes_result_review"]
        == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_v0"
    )
    assert selection["consumes_result_review_pointer"] == (
        "formal/docs/release/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0.json"
    )
    assert selection["computational_physics_stack_status"] == "CLOSED_BOUNDED_NONCLAIM"


def test_main_physics_target_selection_after_closeout_selects_exactly_one_main_target() -> None:
    selection = _json(SELECTION_PATH)
    assert selection["selection_status"] == "selected_one_main_target_nonclaim"
    assert selection["selected_target"] == EXPECTED_SELECTED_TARGET
    assert selection["selected_target_kind"] == "main_release_gap_review_preparation_only"
    assert selection["selected_target_outside_computational_physics_stack"] is True
    assert selection["selection_count"] == 1
    assert selection["candidate_target_count"] == 3
    assert selection["selection_executes_target"] is False
    assert selection["selected_target_execution_status"] == "not_executed_by_this_packet"
    assert selection["next_action"] == EXPECTED_SELECTED_TARGET
    assert (
        selection["next_action_scope"]
        == "MAIN_PROJECT_TARGET_PREPARATION_ONLY_NO_COMPUTATIONAL_PHYSICS_EXECUTION"
    )


def test_main_physics_target_selection_after_closeout_verifies_current_repo_live_target() -> None:
    selection = _json(SELECTION_PATH)
    loop = _json(LOOP_REGISTRY_PATH)
    v01_review = _json(V01_REVIEW_PATH)
    readout = selection["current_repo_live_target_readout"]
    assert (
        "select_next_post_v01_alpha_manifest_enrollment_bounded_attack"
        in loop["next_strict_target_coverage"]
    )
    assert any(
        item["workstream_id"] == "v01_alpha_governance_manifest_enrollment_result_review"
        and item["status"] in {"active", "paused"}
        for item in loop["workstreams"]
    )
    assert v01_review["recommended_selector_choice"] == EXPECTED_SELECTED_TARGET
    assert v01_review["review_executes_selector_choice"] is False
    assert (
        readout["loop_registry_live_next_target"]
        == "select_next_post_v01_alpha_manifest_enrollment_bounded_attack"
    )
    assert (
        readout["loop_registry_active_lane"]
        == "v01_alpha_governance_manifest_enrollment_result_review"
    )
    assert readout["selector_review_recommended_choice"] == EXPECTED_SELECTED_TARGET
    assert readout["workstream_recommended_selector_choice"] == EXPECTED_SELECTED_TARGET
    assert readout["workstream_selector_choice_executed"] == "no"


def test_main_physics_target_selection_after_closeout_candidate_decisions_and_gap_checks() -> None:
    selection = _json(SELECTION_PATH)
    assert {row["target"]: row["decision"] for row in selection["candidate_targets"]} == {
        "prepare_v01_alpha_release_packet_gap_review": "selected",
        "assemble_v01_alpha_public_release_packet": "deferred",
        "return_to_full_pillar_target_map_next_lane_selection": "deferred",
    }
    assert selection["gap_review_required_checks"] == [
        "pillar/seam coverage ledger completeness",
        "claim/evidence ledger completeness",
        "equation ledger completeness",
        "blocker ledger completeness",
        "Lean release index audit rows",
        "public summary readiness",
        "expert review packet readiness",
        "remaining unmigrated release-facing labels",
        "remaining draft/deferred rows",
    ]


def test_main_physics_target_selection_after_closeout_forbidden_effects_false_and_no_claim_language() -> None:
    selection = _json(SELECTION_PATH)
    forbidden = selection["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = (
        json.dumps(selection, sort_keys=True)
        + "\n"
        + _read(ROADMAP_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_main_physics_target_selection_after_closeout_acceptance_criteria_and_determinism() -> None:
    selection = _json(SELECTION_PATH)
    for key, value in selection["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_selection(
        closeout_review_path=CLOSEOUT_REVIEW_PATH,
        loop_registry_path=LOOP_REGISTRY_PATH,
        v01_review_path=V01_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_selection(
        closeout_review_path=CLOSEOUT_REVIEW_PATH,
        loop_registry_path=LOOP_REGISTRY_PATH,
        v01_review_path=V01_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert selection == generated_1


def test_main_physics_target_selection_after_closeout_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_v0",
        "formal/docs/release/MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_20260515_v0.json",
        "formal/python/tools/main_physics_target_selection_after_computational_physics_closeout_report.py",
        "formal/python/tests/test_main_physics_target_selection_after_computational_physics_closeout_gate.py",
        "MAIN_PHYSICS_TARGET_SELECTION_RESUMED_AFTER_COMPUTATIONAL_PHYSICS_NONCLAIM_STACK_CLOSEOUT",
        "prepare_v01_alpha_release_packet_gap_review",
    ]
    for ref in refs:
        assert ref in roadmap_text
        assert ref in physics_text
    assert "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_STATUS_v0: SELECTED_ONE_MAIN_TARGET_NONCLAIM" in roadmap_text
