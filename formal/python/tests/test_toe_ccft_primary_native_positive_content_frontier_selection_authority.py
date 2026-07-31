from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY = RELEASE / "TOE_CCFT_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_SELECTION_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_CCFT_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_SELECTION_AUTHORITY_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
TARGET = "select_ccft_as_primary_native_positive_content_frontier_v0"


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_is_narrow_and_nonexecuting() -> None:
    value = _load(AUTHORITY)
    assert value["authorized_target"] == TARGET
    assert value["authorization_status"] == "AUTHORIZED_NOT_EXECUTED"
    assert len(value["authorized_candidate_lanes"]) == 5
    assert "PREPARE_INSTALL_OR_OPEN_A_CCFT_BOUNDED_PROGRAM" in value["prohibited_actions"]
    assert "EXECUTE_A_NEW_SCIENTIFIC_CALCULATION" in value["prohibited_actions"]


def test_all_authorized_inputs_are_hash_bound() -> None:
    value = _load(AUTHORITY)
    assert len(value["authorized_inputs"]) == 7
    for row in value["authorized_inputs"]:
        path = REPO_ROOT / row["path"]
        assert path.is_file()
        assert _sha256(path) == row["sha256"]


def test_required_scope_caveats_are_preserved() -> None:
    caveats = _load(AUTHORITY)["mandatory_evidence_caveats"]
    assert caveats["repository_claim_exhaustion_established"] is False
    assert caveats["custody_records_outside_bounded_deep_review"] == 12923
    assert caveats["ccft_coherence_claim_count_in_reconciliation"] == 242
    assert caveats["ccft_coherence_bounded_family_readiness"] == "BLOCKED_BY_MISSING_DEFINITION"
    assert caveats["ccft_currently_coherent_candidate_count"] == 0


def test_independent_review_accepts_only_the_selection_authority() -> None:
    review = _load(REVIEW)
    assert review["review_result"] == "PASS"
    assert all(review["checks"].values())
    assert review["independent_conclusion"] == (
        "CCFT_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_SELECTION_AUTHORITY_IS_NARROW_COMPLETE_AND_NONEXECUTING"
    )


def test_registry_retains_the_authorized_workstream() -> None:
    registry = _load(REGISTRY)
    rows = [row for row in registry["workstreams"] if row.get("workstream_id") == TARGET]
    assert len(rows) == 1
    row = rows[0]
    assert row["authorization_evidence"].endswith(
        "ToeCCFTPrimaryNativePositiveContentFrontierSelectionAuthority.lean"
    )
    assert row["report"].endswith(
        "TOE_CCFT_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_SELECTION_AUTHORITY_REVIEW_v0.json"
    )
    assert row["ccft_resumed"] == "no"

