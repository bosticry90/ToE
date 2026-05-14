from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
SELECTION_JSON = (
    RELEASE_DIR
    / "POST_V01_ALPHA_RELEASE_STANDARD_FOUNDATION_BOUNDED_ATTACK_SELECTION_20260513_v0.json"
)
SELECTION_MD = (
    RELEASE_DIR / "POST_V01_ALPHA_RELEASE_STANDARD_FOUNDATION_BOUNDED_ATTACK_SELECTION_v0.md"
)
REVIEW_JSON = (
    RELEASE_DIR / "TOE_V01_ALPHA_RELEASE_STANDARD_FOUNDATION_RESULT_REVIEW_20260513_v0.json"
)
MANIFEST_PATH = RELEASE_DIR / "GOVERNANCE_TEST_MANIFEST_v1.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_post_v01_alpha_foundation_selector_consumes_green_review() -> None:
    selection = _json(SELECTION_JSON)
    review = _json(REVIEW_JSON)

    assert selection["schema_id"] == (
        "POST_V01_ALPHA_RELEASE_STANDARD_FOUNDATION_BOUNDED_ATTACK_SELECTION_v0"
    )
    assert selection["result_token"] == (
        "POST_V01_ALPHA_RELEASE_STANDARD_FOUNDATION_NEXT_ATTACK_SELECTED"
    )
    assert selection["consumed_target"] == (
        "select_next_post_v01_alpha_release_standard_foundation_bounded_attack"
    )
    assert selection["consumed_review_token"] == review["result_token"]
    assert selection["consumed_review_path"] == str(
        REVIEW_JSON.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert selection["required_foundation_status"] == review["foundation_status"]
    assert selection["required_release_scope"] == review["release_scope_confirmed"]

    for key, expected in selection["required_full_suite_status"].items():
        assert review["full_suite_status"][key] == expected


def test_post_v01_alpha_foundation_selector_selects_manifest_prep_only() -> None:
    selection = _json(SELECTION_JSON)

    assert selection["selection_status"] == "selected_one_next_bounded_target"
    assert selection["selected_next_target"] == (
        "prepare_v01_alpha_governance_manifest_enrollment"
    )
    assert selection["selected_next_target_kind"] == (
        "manifest_enrollment_preparation_only"
    )
    assert selection["selection_count"] == 1
    assert selection["selection_executes_target"] == "no"
    assert {
        row["target"]: row["decision"] for row in selection["candidate_targets"]
    } == {
        "prepare_v01_alpha_governance_manifest_enrollment": "selected",
        "return_to_full_pillar_target_map_next_lane_selection": "deferred",
    }


def test_post_v01_alpha_foundation_selector_does_not_enroll_manifest() -> None:
    selection = _json(SELECTION_JSON)
    manifest_text = _read(MANIFEST_PATH)

    assert selection["governance_manifest_enrollment_authorized"] is False
    assert selection["governance_manifest_enrollment_performed"] is False
    assert selection["governance_manifest_enrollment_status"] == "not_enrolled"
    assert selection["public_release_completion_authorized"] is False
    assert selection["release_gate_baseline_authorized"] is False

    assert "formal/python/tests/test_toe_v01_alpha_release_standard_gate.py" not in manifest_text
    assert (
        "formal/python/tests/test_toe_v01_alpha_release_standard_foundation_review_gate.py"
        not in manifest_text
    )
    assert (
        "formal/python/tests/test_post_v01_alpha_release_standard_foundation_bounded_attack_selection_gate.py"
        not in manifest_text
    )
    assert "TOE_V01_ALPHA_RELEASE_GATE_ENROLLED" not in manifest_text


def test_post_v01_alpha_foundation_selector_preserves_nonclaim_boundary() -> None:
    selection = _json(SELECTION_JSON)
    md_text = _read(SELECTION_MD)

    required_nonclaims = {
        "NC-NO-MASTER-ACTION-PROMOTION",
        "NC-NO-PILLAR-COMPLETION",
        "NC-NO-SEAM-CLOSURE",
        "NC-NO-PHASE2",
        "NC-NO-EMPIRICAL-ADEQUACY",
        "NC-NO-CANONICAL-TOE",
        "NC-NO-QFT-GR-SOURCE-MAP-CLOSURE",
    }
    assert set(selection["nonclaim_ids"]) == required_nonclaims

    for phrase in [
        "v0.1-alpha public release complete",
        "GOVERNANCE_TEST_MANIFEST_v1 enrollment",
        "master-action promotion",
        "pillar completion",
        "seam closure",
        "Phase 2 readiness",
        "empirical adequacy",
        "canonical ToE status",
        "QFT-GR source-map closure",
    ]:
        assert phrase in selection["not_authorized_claims"]

    for phrase in [
        "Selection only.",
        "Governance manifest enrollment is not performed",
        "does not complete v0.1-alpha public release",
        "does not authorize master-action promotion",
        "QFT-GR source-map closure",
    ]:
        assert phrase in md_text
