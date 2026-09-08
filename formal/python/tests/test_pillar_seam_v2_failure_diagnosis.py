from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DIAGNOSIS_PATH = REPO_ROOT / "formal" / "docs" / "release" / (
    "PILLAR_SEAM_V2_DETERMINISTIC_FAILURE_DIAGNOSIS_20260720_v0.json"
)
ACCEPTED_REVIEW_PATH = (
    "formal/docs/release/"
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_20260712_v0.json"
)


def test_v2_failure_diagnosis_binds_first_cause_and_all_eight_cascades() -> None:
    diagnosis = json.loads(DIAGNOSIS_PATH.read_text(encoding="utf-8"))
    committed = subprocess.run(
        ["git", "show", f"HEAD:{ACCEPTED_REVIEW_PATH}"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    ).stdout

    assert diagnosis["phase_a_evidence"]["failed"] == 8
    assert sum(group["count"] for group in diagnosis["failure_groups"]) == 8
    assert diagnosis["first_cause"]["expected_committed_lf_sha256"] == hashlib.sha256(
        committed
    ).hexdigest()
    assert diagnosis["first_cause"]["scientific_payload_difference"] is False


def test_v2_correction_is_only_canonical_text_custody() -> None:
    diagnosis = json.loads(DIAGNOSIS_PATH.read_text(encoding="utf-8"))
    attributes = (REPO_ROOT / ".gitattributes").read_text(encoding="utf-8")

    for zone in diagnosis["authorized_correction"]["zones"]:
        assert f"{zone} text eol=lf" in attributes
    assert set(diagnosis["scientific_boundaries"].values()) == {False}
