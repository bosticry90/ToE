from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
REVIEW_JSON = RELEASE_DIR / "TOE_V01_ALPHA_RELEASE_STANDARD_FOUNDATION_RESULT_REVIEW_20260513_v0.json"

PUBLIC_SURFACES = [
    REPO_ROOT / "README.md",
    REPO_ROOT / "State_of_the_Theory.md",
    RELEASE_DIR / "CURRENT_AUTHORITATIVE_SURFACES_v0.md",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_foundation_review_consumes_pre_manifest_foundation() -> None:
    review = _json(REVIEW_JSON)

    assert review["result_token"] == "TOE_V01_ALPHA_RELEASE_STANDARD_FOUNDATION_REVIEW_CONSUMED_PRE_MANIFEST"
    assert review["consumed_target"] == "review_toe_v01_alpha_release_standard_foundation_result"
    assert review["foundation_status"] == "PRE_MANIFEST_FOUNDATION_FULL_WRAPPER_VALIDATED"
    assert review["release_scope_confirmed"] == "FULL_PILLAR_FULL_SEAM_RELEASE_STANDARD"
    assert review["selected_next_target"] == "select_next_post_v01_alpha_release_standard_foundation_bounded_attack"

    required_tokens = {
        "TOE_V01_ALPHA_RELEASE_STANDARD_LANE_SELECTED",
        "TOE_V01_ALPHA_RELEASE_STANDARD_PREPARED_FULL_PILLAR_SEAM_SCOPE",
        "TOE_V01_ALPHA_PILLAR_SEAM_COVERAGE_LEDGER_SEEDED",
        "TOE_V01_ALPHA_CLAIM_EVIDENCE_LEDGER_SEEDED",
        "TOE_V01_ALPHA_LEAN_RELEASE_SPINE_PREPARED",
    }
    assert set(review["consumed_tokens"]) == required_tokens

    for rel_path in review["prepared_artifacts"].values():
        assert (REPO_ROOT / rel_path).exists(), f"Review references missing prepared artifact: {rel_path}"


def test_v01_alpha_foundation_review_is_pre_manifest_only() -> None:
    review = _json(REVIEW_JSON)

    assert review["governance_manifest_enrollment_authorized"] is False
    assert review["governance_manifest_enrollment_status"] == "not_enrolled"
    assert review["public_release_completion_authorized"] is False
    assert review["full_suite_status"]["release_interpretation"] == (
        "full wrapper validation green for the pre-manifest foundation; governance manifest enrollment "
        "remains unauthorized until a separate enrollment packet"
    )
    assert review["full_suite_status"]["run_governance_ps1"] == "passed"
    assert review["full_suite_status"]["run_pytest_ps1"] == "passed"
    assert review["full_suite_status"]["run_lean_ps1"] == "passed"
    assert review["full_suite_status"]["git_diff_check"] == "passed"
    assert review["full_suite_status"]["observed"]["run_pytest_ps1"] == "6776 passed, 235 skipped"


def test_public_surfaces_preserve_release_standard_noncompletion_posture() -> None:
    for surface in PUBLIC_SURFACES:
        text = _read(surface)
        assert "release-standard" in text or "release standard" in text
        assert "not complete" in text or "not as a completed release" in text
        assert "no master-action promotion" in text
        assert "no pillar completion" in text
        assert "no seam closure" in text
        assert "no QFT-GR source-map closure" in text
