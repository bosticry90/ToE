from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
LEAN_SURFACE = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "V01AlphaGovernanceManifestEnrollmentResultReview.lean"
)
AGGREGATE = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REVIEW_JSON = (
    RELEASE_DIR
    / "V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_20260513_v0.json"
)
ENROLLMENT_JSON = RELEASE_DIR / "V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_20260513_v0.json"
MANIFEST_PATH = RELEASE_DIR / "GOVERNANCE_TEST_MANIFEST_v1.json"
PUBLIC_SURFACES = [
    REPO_ROOT / "README.md",
    REPO_ROOT / "State_of_the_Theory.md",
    RELEASE_DIR / "CURRENT_AUTHORITATIVE_SURFACES_v0.md",
]

REPORT_ID = "V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_v0"
REVIEW_TOKEN = "TOE_V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_CONSUMED"
ENROLLMENT_TOKEN = "TOE_V01_ALPHA_RELEASE_GATE_ENROLLED"
CURRENT_TARGET = "review_v01_alpha_governance_manifest_enrollment_result"
NEXT_TARGET = "select_next_post_v01_alpha_manifest_enrollment_bounded_attack"
RECOMMENDED_SELECTOR_CHOICE = "prepare_v01_alpha_release_packet_gap_review"
EXPECTED_COUNT = 346
EXPECTED_HASH = "e5964369e2e1033b805e2838d3aa18fc22cd1b8a5deb1d0478c8000705f87dfb"
FOCUSED_GATE = "formal/python/tests/test_v01_alpha_governance_manifest_enrollment_result_review_gate.py"

REVIEW_EVIDENCE = str(LEAN_SURFACE.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REVIEW_JSON.relative_to(REPO_ROOT)).replace("\\", "/")
ENROLLMENT_EVIDENCE = str(ENROLLMENT_JSON.relative_to(REPO_ROOT)).replace("\\", "/")

STABLE_NONCLAIM_IDS = {
    "NC-NO-MASTER-ACTION-PROMOTION",
    "NC-NO-PILLAR-COMPLETION",
    "NC-NO-SEAM-CLOSURE",
    "NC-NO-PHASE2",
    "NC-NO-EMPIRICAL-ADEQUACY",
    "NC-NO-CANONICAL-TOE",
    "NC-NO-QFT-GR-SOURCE-MAP-CLOSURE",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _sha256_joined(items: list[str]) -> str:
    return hashlib.sha256("\n".join(items).encode("utf-8")).hexdigest()


def test_v01_alpha_enrollment_result_review_lean_surface_is_imported() -> None:
    text = _read(LEAN_SURFACE)
    aggregate_text = _read(AGGREGATE)

    for token in {
        "v01_alpha_governance_manifest_enrollment_result_review_v0",
        CURRENT_TARGET,
        ENROLLMENT_TOKEN,
        REVIEW_TOKEN,
        REPORT_EVIDENCE,
        NEXT_TARGET,
        RECOMMENDED_SELECTOR_CHOICE,
        "V01AlphaGovernanceManifestEnrollmentResultReviewStatus",
        "v01_alpha_governance_manifest_enrollment_result_review_consumes_target_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_consumes_token_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_token_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_count_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_hash_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_enrolled_tests_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_manifest_confirmed_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_full_validation_green_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_public_surfaces_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_next_target_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_recommends_gap_review_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_selector_choice_not_executed_v0",
    }:
        assert token in text

    for theorem in {
        "v01_alpha_governance_manifest_enrollment_result_review_no_unrelated_gate_enrollment_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_no_public_release_completion_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_no_master_action_promotion_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_no_pillar_completion_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_no_seam_closure_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_no_phase2_readiness_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_no_empirical_adequacy_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_no_canonical_toe_v0",
        "v01_alpha_governance_manifest_enrollment_result_review_no_qft_gr_source_map_closure_v0",
    }:
        assert theorem in text

    assert (
        "import ToeFormal.Derivation.V01AlphaGovernanceManifestEnrollmentResultReview"
        in aggregate_text
    )


def test_v01_alpha_enrollment_result_review_report_consumes_enrollment() -> None:
    review = _json(REVIEW_JSON)
    enrollment = _json(ENROLLMENT_JSON)

    assert review["schema_id"] == REPORT_ID
    assert review["classification"] == "P-POLICY/nonclaim"
    assert review["review_status"] == "completed_result_consumed"
    assert review["result_token"] == REVIEW_TOKEN
    assert review["consumed_target"] == CURRENT_TARGET
    assert review["consumed_enrollment_token"] == enrollment["result_token"] == ENROLLMENT_TOKEN
    assert review["consumed_enrollment_path"] == ENROLLMENT_EVIDENCE
    assert review["review_surface"] == REVIEW_EVIDENCE
    assert review["focused_gate"] == FOCUSED_GATE
    assert review["release_scope_confirmed"] == enrollment["release_scope_confirmed"]
    assert review["enrollment_status_confirmed"] == enrollment["enrollment_status"]
    assert review["governance_manifest_enrollment_confirmed"] is True
    assert review["release_standard_artifacts_governed_baseline"] is True


def test_v01_alpha_enrollment_result_review_confirms_manifest_count_and_hash() -> None:
    review = _json(REVIEW_JSON)
    enrollment = _json(ENROLLMENT_JSON)
    manifest = _json(MANIFEST_PATH)
    group = manifest["groups"]["governance_pytests"]
    tests = group["tests"]

    assert review["manifest_path"] == "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"
    assert review["current_governance_pytest_expected_count"] == EXPECTED_COUNT
    assert review["current_governance_pytest_expected_sha256"] == EXPECTED_HASH
    assert enrollment["current_governance_pytest_expected_count"] == EXPECTED_COUNT
    assert enrollment["current_governance_pytest_expected_sha256"] == EXPECTED_HASH

    assert group["expected_count"] == EXPECTED_COUNT
    assert group["expected_sha256"] == EXPECTED_HASH
    assert len(tests) == EXPECTED_COUNT
    assert _sha256_joined(tests) == EXPECTED_HASH

    assert review["enrolled_tests_confirmed"] == enrollment["enrolled_tests"]
    assert set(review["enrolled_tests_confirmed"]).issubset(set(tests))
    assert FOCUSED_GATE not in tests


def test_v01_alpha_enrollment_result_review_records_validation_and_next_selector() -> None:
    review = _json(REVIEW_JSON)

    assert review["review_effect"] == {
        "enrollment_result_consumed": True,
        "manifest_count_confirmed": True,
        "manifest_hash_confirmed": True,
        "public_surfaces_manifest_enrolled_not_complete_confirmed": True,
        "full_validation_green_confirmed": True,
        "post_enrollment_selector_target_selected": True,
        "release_packet_gap_review_recommended": True,
        "selector_choice_executed": False,
        "release_packet_assembled": False,
        "unrelated_gate_enrollment_performed": False,
    }
    assert review["full_suite_status"]["run_governance_ps1"] == "passed"
    assert review["full_suite_status"]["run_pytest_ps1"] == "passed"
    assert review["full_suite_status"]["run_lean_ps1"] == "passed"
    assert review["full_suite_status"]["git_diff_check"] == "passed"
    assert review["full_suite_status"]["git_diff_exit_code"] == "passed_after_commit"
    assert review["full_suite_status"]["observed"]["run_pytest_ps1"] == (
        "6782 passed, 235 skipped"
    )
    assert review["full_suite_status"]["observed"]["run_lean_ps1"] == (
        "Build completed successfully (8008 jobs)"
    )

    assert review["selected_next_target"] == NEXT_TARGET
    assert review["recommended_selector_choice"] == RECOMMENDED_SELECTOR_CHOICE
    assert review["review_executes_selector_choice"] is False
    assert {
        row["target"]: row["recommendation"] for row in review["candidate_selector_targets"]
    } == {
        "prepare_v01_alpha_release_packet_gap_review": "recommended",
        "assemble_v01_alpha_public_release_packet": "deferred",
        "return_to_full_pillar_target_map_next_lane_selection": "deferred",
    }
    assert review["gap_review_required_checks"] == [
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
    assert review["next_action_after_result_review"] == NEXT_TARGET


def test_v01_alpha_enrollment_result_review_preserves_nonclaim_boundaries() -> None:
    review = _json(REVIEW_JSON)

    assert set(review["nonclaim_ids"]) == STABLE_NONCLAIM_IDS
    assert review["forbidden_effects"] == [
        "V01_ALPHA_PUBLIC_RELEASE_COMPLETION",
        "MASTER_ACTION_PROMOTION",
        "PILLAR_COMPLETION",
        "SEAM_CLOSURE",
        "PHASE_2_READINESS",
        "EMPIRICAL_ADEQUACY",
        "CANONICAL_TOE_STATUS",
        "QFT_GR_SOURCE_MAP_CLOSURE",
        "UNRELATED_GATE_ENROLLMENT",
    ]
    assert review["nonclaim_boundaries"] == {
        "public_release_completion_authorized": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "unrelated_gate_enrollment_authorized": False,
    }

    for phrase in [
        "v0.1-alpha public release complete",
        "master-action promotion",
        "pillar completion",
        "seam closure",
        "Phase 2 readiness",
        "empirical adequacy",
        "canonical ToE status",
        "QFT-GR source-map closure",
        "additional governance gate enrollment",
        "release packet assembly",
    ]:
        assert phrase in review["not_authorized_claims"]

    assert "manifest-enrolled but not complete" in review["acceptance_condition"]


def test_v01_alpha_enrollment_result_review_public_surfaces() -> None:
    for surface in PUBLIC_SURFACES:
        text = _read(surface)
        assert ENROLLMENT_TOKEN in text
        assert REVIEW_TOKEN in text
        assert NEXT_TARGET in text
        assert RECOMMENDED_SELECTOR_CHOICE in text
        assert "manifest-enrolled" in text
        assert "not complete" in text or "not as a completed release" in text
        assert "no master-action promotion" in text
        assert "no pillar completion" in text
        assert "no seam closure" in text
        assert "no QFT-GR source-map closure" in text

    authoritative = _read(RELEASE_DIR / "CURRENT_AUTHORITATIVE_SURFACES_v0.md")
    assert REPORT_EVIDENCE in authoritative
