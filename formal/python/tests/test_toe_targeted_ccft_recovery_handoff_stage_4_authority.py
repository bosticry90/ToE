from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
AUTHORITY = RELEASE / "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_STAGE_4_OPEN_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_STAGE_4_OPEN_AUTHORITY_REVIEW_v0.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_four_scope() -> None:
    authority = read(AUTHORITY)
    assert authority["status"] == "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_4_OPEN_ONLY"
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": "f6e792eae759877e5e0e6a263834dbdfd96fa8b2a1918a8a038257ab767af254",
        "canonical_target": "select_toe_post_targeted_ccft_recovery_construction_handoff_v0",
        "semantic_stage_id": "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF",
        "stage_number": 4,
    }


def test_authority_binds_positive_threshold_inputs() -> None:
    summary = read(AUTHORITY)["scientific_input_summary"]
    assert summary["exact_contracts_recovered"] == 4
    assert summary["cp_nlse_exact_contracts"] == 1
    assert summary["lcrd_v3_exact_contracts"] == 3
    assert summary["positive_recovery_threshold_satisfied"] is True


def test_authority_hashes_reproduce() -> None:
    authority = read(AUTHORITY)
    for binding in authority["authorized_input_bindings"] + authority["evidence_bindings"]:
        assert sha(ROOT / binding["path"]) == binding["sha256"]


def test_handoff_is_nonautomatic_and_exit_first() -> None:
    boundary = read(AUTHORITY)["frozen_handoff_boundary"]
    assert boundary["construction_preparation_authorized"] is False
    assert boundary["theorem_discovery_lane_authorized"] is False
    assert boundary["historical_recovery_after_handoff_authorized"] is False
    assert boundary["mandatory_exit_precedes_any_construction_preparation"] is True


def test_review_accepts_authority_without_result() -> None:
    review = read(REVIEW)
    assert review["accepted"] is True
    assert review["handoff_selected"] is False
    assert review["construction_or_theorem_work_authorized"] is False
    assert review["scientific_result_created"] is False
    assert all(review["checks"].values())
