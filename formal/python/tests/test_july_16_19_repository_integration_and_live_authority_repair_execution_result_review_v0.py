from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = ROOT / (
    "formal/docs/release/"
    "JULY_16_19_REPOSITORY_INTEGRATION_AND_LIVE_AUTHORITY_REPAIR_"
    "EXECUTION_RESULT_REVIEW_20260727_v0.json"
)
REGISTRY_PATH = ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
IMPLEMENTATION_TIP = "593a64cdf1f54302f9da1479dad039689e66ffba"
BASELINE = "a099c6867493d48a7aaba2f79bf2e29ecbf2cfd3"
ORIGIN_MAIN_AT_REVIEW = "75af1d110a57df26344ca151ccd26b9f5c1f7736"
REVIEW_SHA256 = (
    "79a68a13b6d1d58115ad6c723e1e2cb39a3e3c6956ea34f858ed0f4a399bb8ff"
)


def _review() -> dict:
    value = json.loads(REVIEW_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _git(*args: str) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
    ).stdout.strip()


def test_result_review_is_hash_exact_and_accepts_only_maintenance() -> None:
    review = _review()
    assert _sha256(REVIEW_PATH) == REVIEW_SHA256
    assert review["verdict"] == (
        "ACCEPTED_MAINTENANCE_INTEGRATION_COMPLETE_"
        "SCIENTIFIC_RECONCILIATION_PENDING"
    )
    assert review["implementation_tip"]["commit"] == IMPLEMENTATION_TIP
    assert review["closeout"]["maintenance_execution_complete"] is True
    assert review["closeout"]["scientific_authority_advance_authorized_by_this_review"] is False


def test_validated_history_is_restructured_linear_and_fully_accounted() -> None:
    review = _review()
    history = review["history_accounting"]
    assert _git("merge-base", BASELINE, IMPLEMENTATION_TIP) == BASELINE
    assert int(_git("rev-list", "--count", f"{BASELINE}..{IMPLEMENTATION_TIP}")) == 47
    assert _git("rev-list", "--merges", f"{BASELINE}..{IMPLEMENTATION_TIP}") == ""
    assert _git("rev-parse", f"{IMPLEMENTATION_TIP}^{{tree}}") == (
        review["implementation_tip"]["tree"]
    )
    assert int(_git("rev-list", "--count", f"{ORIGIN_MAIN_AT_REVIEW}..{BASELINE}")) == 143
    assert history["source_commits_requiring_disposition"] == 44
    assert history["source_commits_with_recorded_disposition"] == 44
    assert history["blind_merge_used"] is False
    assert history["restructured_architecture_prevailed"] is True
    assert history["only_intended_commits_accounted_for"] is True


def test_all_protected_lineages_resolve_to_the_reviewed_commits() -> None:
    for lineage in _review()["protected_lineages"].values():
        assert _git("rev-parse", f"{lineage['tag']}^{{}}") == lineage["commit"]


def test_reconciliation_records_and_deletions_are_exact() -> None:
    review = _review()
    records = review["committed_reconciliation_records"]
    for record in records.values():
        assert _sha256(ROOT / record["path"]) == record["sha256"]
    observed_deletions = sorted(
        line.split("\t", 1)[1]
        for line in _git(
            "diff", "--name-status", f"{BASELINE}..{IMPLEMENTATION_TIP}"
        ).splitlines()
        if line.startswith("D\t")
    )
    assert observed_deletions == sorted(
        records["front_door_disposition"]["explained_baseline_relative_deletions"]
    )
    assert review["front_door_and_deletion_review"]["unexplained_tracked_deletions"] == 0


def test_validation_matrix_distinguishes_current_pass_from_historical_record() -> None:
    validation = _review()["validation"]
    assert validation["immutable_current_control_profile_v9"]["pytest_exit_code"] == 0
    assert validation["immutable_current_control_profile_v9"]["failed"] == 0
    assert validation["split_tranche_profile"]["current_overlay_verdict"] == "PASS"
    assert validation["split_tranche_profile"][
        "historical_overlay_current_verdict_influence"
    ] == "NONE"
    assert validation["split_tranche_profile"]["historical_overlay_verdict"] == (
        "COMPLETE_WITH_RECORDED_FAILURES"
    )
    assert validation["full_lean_build"]["exit_code"] == 0
    assert validation["fresh_detached_clean_checkout"]["verdict"] == "PASS"
    assert validation["aggregate_generation"]["verdict"] == "PASS"
    assert validation["scientific_authority_consistency"]["verdict"] == "PASS"
    assert validation["git_diff_check"]["verdict"] == "PASS"


def test_scientific_target_and_all_prohibited_effects_remain_frozen() -> None:
    review = _review()
    registry = json.loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    firewall = review["scientific_firewall"]
    assert registry["current_projection_v0"]["current_target"] == (
        firewall["canonical_scientific_target"]
    )
    for field, value in firewall.items():
        if field == "canonical_scientific_target":
            continue
        assert value is False
