from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import pillar_v1_source_identity


REPO_ROOT = find_repo_root(Path(__file__))
RESULT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "REPOSITORY_PILLAR_V1_HISTORICAL_CURRENT_SOURCE_ROLE_SEPARATION_"
    "REPAIR_RESULT_20260725_v0.json"
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        stdout=subprocess.PIPE,
    ).stdout.decode("ascii").strip()


def test_result_binds_both_versioned_identity_contracts() -> None:
    result = json.loads(RESULT_PATH.read_bytes())
    assert result["schema_id"].endswith("REPAIR_RESULT_20260725_v0")
    for contract in result["identity_contracts"]:
        path = REPO_ROOT / contract["path"]
        assert _sha256(path) == contract["sha256"]
        payload = pillar_v1_source_identity.load_contract(path)
        assert payload["contract_version"] == contract["contract_version"]
        assert payload["current_relative_to_commit"] == contract[
            "current_relative_to_commit"
        ]


def test_result_commit_relative_git_identities_resolve_exactly() -> None:
    result = json.loads(RESULT_PATH.read_bytes())
    for identity in result["identities"].values():
        revision = f"{identity['relative_to_commit']}:{identity['tracked_path']}"
        assert _git("rev-parse", revision) == identity["git_blob"]
        raw = subprocess.run(
            ["git", "cat-file", "blob", identity["git_blob"]],
            cwd=REPO_ROOT,
            check=True,
            stdout=subprocess.PIPE,
        ).stdout
        assert hashlib.sha256(raw).hexdigest() == identity["sha256"]


def test_result_preserves_historical_review_and_scientific_boundaries() -> None:
    result = json.loads(RESULT_PATH.read_bytes())
    custody = result["historical_custody"]
    review_path = REPO_ROOT / custody["review_path"]
    assert _sha256(review_path) == custody["review_sha256"]
    assert review_path.stat().st_size == custody["review_bytes"]
    assert custody["historical_review_source_pin_preserved"] is True
    assert custody["historical_review_rewritten"] is False
    assert result["scientific_posture"] == "B-BLOCKED"
    assert result["v2_enrollment"] == "NOT_AUTHORIZED"
    assert result["scientific_resumption"] == "NOT_AUTHORIZED"


def test_result_reports_exact_recovery_and_no_successor_authority() -> None:
    result = json.loads(RESULT_PATH.read_bytes())
    assert result["validation"]["affected_outcomes"] == {
        "expected": 39,
        "recovered": 39,
        "masked_secondary_roots": 0,
    }
    assert result["authorization"]["successor_authority"] == "NONE"
    assert result["scope"]["staging_identity_repair_performed"] is False
    assert result["scope"]["automatic_successor"] is False
