from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qm_gr_criteria_hash_refresh as refresh
from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v2 as v2,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
PACKET_PATH = RELEASE / (
    "REPOSITORY_HASH_REFRESH_AND_TRACKED_BLOB_IDENTITY_REPAIR_PACKET_20260721_v0.json"
)
RESULT_PATH = RELEASE / (
    "REPOSITORY_HASH_REFRESH_AND_TRACKED_BLOB_IDENTITY_REPAIR_RESULT_20260721_v0.json"
)
REVIEW_PATH = RELEASE / (
    "REPOSITORY_HASH_REFRESH_AND_TRACKED_BLOB_IDENTITY_REPAIR_RESULT_REVIEW_20260721_v0.json"
)
AUTHORITY_PATH = RELEASE / "CURRENT_MAINTENANCE_AUTHORITY_v0.json"
ACCEPTED_RESULT_REVIEW_COMMIT = (
    "654ee628096bdb4b1fb98999a3a23a11c2871c18"
)


def _load(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_git_json(commit: str, path: Path) -> dict:
    relative = path.relative_to(REPO_ROOT).as_posix()
    raw = subprocess.check_output(
        ["git", "show", f"{commit}:{relative}"],
        cwd=REPO_ROOT,
    )
    payload = json.loads(raw)
    assert isinstance(payload, dict)
    return payload


def test_repair_result_and_review_are_bound_and_terminal() -> None:
    result = _load(RESULT_PATH)
    review = _load(REVIEW_PATH)
    authority = _load_git_json(ACCEPTED_RESULT_REVIEW_COMMIT, AUTHORITY_PATH)

    assert review["verdict"] == "ACCEPT"
    assert review["result"]["sha256"] == _sha256(RESULT_PATH)
    assert all(review["checks"].values())
    assert set(result["acceptance_results"].values()) == {
        "INDIVIDUALLY_PROVEN",
        "NONE",
        "READ_ONLY_PASS",
        "EMPTY_RELATIVE_TO_PRE_VALIDATION_STATE",
        "GIT_BLOB_BASED",
        "REPRODUCIBLE_FROM_FROZEN_COMMITTED_INPUTS",
        "TEMPORARY_TREE_ONLY_PASS",
    }
    assert authority["current_maintenance_target_status"] == (
        "COMPLETE_ACCEPTED_NO_AUTOMATIC_SUCCESSOR"
    )
    assert authority["independent_result_review"]["sha256"] == _sha256(
        REVIEW_PATH
    )
    boundary = authority["boundary"]
    assert boundary["repair_implementation_cycles_remaining"] == 0
    assert boundary["tracked_source_mutation_authorized"] is False
    assert boundary["test_modification_authorized"] is False
    assert boundary["v2_enrollment_authorized"] is False
    assert boundary["v2_regeneration_authorized"] is False
    assert boundary["first_unit_selector_execution_authorized"] is False


def test_eight_adjudicated_tokens_match_canonical_artifacts() -> None:
    packet = _load(PACKET_PATH)
    rows = packet["token_adjudications"]
    assert len(rows) == 8
    assert refresh.check_expected_hashes(repo_root=REPO_ROOT) == []

    for row in rows:
        containing = (REPO_ROOT / row["containing_file"]).read_bytes()
        expected = _sha256(REPO_ROOT / row["referenced_source"])
        assert row["identity_type"] == "CANONICAL_ARTIFACT_SHA256"
        assert row["proposed_value"] == expected
        assert row["proposed_value"].encode("ascii") in containing
        assert row["old_value"].encode("ascii") not in containing
        assert row["scientific_content_impact"] == "NONE_IDENTITY_METADATA_ONLY"

    test_source = (
        REPO_ROOT / "formal/python/tests/test_qm_gr_criteria_hash_refresh_tool.py"
    ).read_text(encoding="utf-8")
    assert "apply_updates(repo_root=tool.REPO_ROOT)" not in test_source


def test_v2_reconstructs_only_from_recorded_identity_domains() -> None:
    packet, manifest, report = v2.build_artifacts()
    identities = [
        *packet["dependency_closures"]["scientific_input_closure"],
        *packet["dependency_closures"]["implementation_closure"]["artifacts"],
        *packet["dependency_closures"]["environment_closure"][
            "bound_environment_files"
        ],
        packet["prompt_protection"],
        manifest["generator"],
    ]
    assert len(identities) == 28
    assert {item["frozen_commit"] for item in identities} == {v2._frozen_commit()}
    assert {item["identity_type"] for item in identities} == {
        "CANONICAL_ARTIFACT_SHA256",
        "GIT_BLOB_SHA256",
    }
    assert all(v2._identity_matches(item) for item in identities)
    assert v2.PACKET_PATH.read_bytes() == v2.canonical_json_bytes(packet)
    assert v2.MANIFEST_PATH.read_bytes() == v2.canonical_json_bytes(manifest)
    assert v2.REPORT_PATH.read_bytes() == v2.canonical_json_bytes(report)
    assert report["first_unit_selector_authorized"] is False
