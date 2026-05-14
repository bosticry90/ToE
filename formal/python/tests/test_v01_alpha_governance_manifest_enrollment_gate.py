from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
ENROLLMENT_JSON = RELEASE_DIR / "V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_20260513_v0.json"
MANIFEST_PATH = RELEASE_DIR / "GOVERNANCE_TEST_MANIFEST_v1.json"
SELECTION_JSON = (
    RELEASE_DIR
    / "POST_V01_ALPHA_RELEASE_STANDARD_FOUNDATION_BOUNDED_ATTACK_SELECTION_20260513_v0.json"
)
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


def _sha256_joined(items: list[str]) -> str:
    return hashlib.sha256("\n".join(items).encode("utf-8")).hexdigest()


def test_v01_alpha_manifest_enrollment_consumes_selector_and_enrolls_only_release_gates() -> None:
    enrollment = _json(ENROLLMENT_JSON)
    selection = _json(SELECTION_JSON)
    manifest = _json(MANIFEST_PATH)
    group = manifest["groups"]["governance_pytests"]
    tests = group["tests"]

    assert enrollment["result_token"] == "TOE_V01_ALPHA_RELEASE_GATE_ENROLLED"
    assert enrollment["consumed_target"] == "prepare_v01_alpha_governance_manifest_enrollment"
    assert enrollment["consumed_selector_token"] == selection["result_token"]
    assert selection["selected_next_target"] == "prepare_v01_alpha_governance_manifest_enrollment"
    assert enrollment["release_scope_confirmed"] == "FULL_PILLAR_FULL_SEAM_RELEASE_STANDARD"

    assert enrollment["governance_manifest_enrollment_authorized"] is True
    assert enrollment["governance_manifest_enrollment_performed"] is True
    assert enrollment["release_standard_artifacts_governed_baseline"] is True
    assert enrollment["enrollment_status"] == "governance_manifest_enrolled"
    assert enrollment["selected_next_target"] == "review_v01_alpha_governance_manifest_enrollment_result"

    enrolled_tests = enrollment["enrolled_tests"]
    assert len(enrolled_tests) == 5
    assert set(enrolled_tests).issubset(set(tests))
    assert "formal/python/tests/test_v01_alpha_governance_manifest_enrollment_gate.py" in tests

    assert group["expected_count"] == enrollment["current_governance_pytest_expected_count"]
    assert group["expected_sha256"] == enrollment["current_governance_pytest_expected_sha256"]
    assert len(tests) == group["expected_count"]
    assert _sha256_joined(tests) == group["expected_sha256"]
    assert tests[-1] == "formal/python/tests/test_sql_integrity_snapshot_tool.py"


def test_v01_alpha_manifest_enrollment_preserves_pre_release_nonclaim_boundary() -> None:
    enrollment = _json(ENROLLMENT_JSON)

    assert enrollment["public_release_completion_authorized"] is False
    assert enrollment["scientific_status_change_authorized"] is False

    expected_nonclaims = {
        "NC-NO-MASTER-ACTION-PROMOTION",
        "NC-NO-PILLAR-COMPLETION",
        "NC-NO-SEAM-CLOSURE",
        "NC-NO-PHASE2",
        "NC-NO-EMPIRICAL-ADEQUACY",
        "NC-NO-CANONICAL-TOE",
        "NC-NO-QFT-GR-SOURCE-MAP-CLOSURE",
    }
    assert set(enrollment["nonclaim_ids"]) == expected_nonclaims

    for phrase in [
        "v0.1-alpha public release complete",
        "master-action promotion",
        "pillar completion",
        "seam closure",
        "Phase 2 readiness",
        "empirical adequacy",
        "canonical ToE status",
        "QFT-GR source-map closure",
    ]:
        assert phrase in enrollment["not_authorized_claims"]


def test_public_surfaces_mark_manifest_enrolled_but_not_public_release_complete() -> None:
    for surface in PUBLIC_SURFACES:
        text = _read(surface)
        assert "TOE_V01_ALPHA_RELEASE_GATE_ENROLLED" in text
        assert "manifest-enrolled" in text
        assert "not complete" in text or "not as a completed release" in text
        assert "no master-action promotion" in text
        assert "no pillar completion" in text
        assert "no seam closure" in text
        assert "no QFT-GR source-map closure" in text
