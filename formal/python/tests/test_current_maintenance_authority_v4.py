from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
AUTHORITY_PATH = ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v4.json"
POINTER_PATH = (
    ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0.json"
)
REVIEW_PATH = (
    ROOT
    / "formal/docs/release"
    / "CANONICAL_TEXT_ATTRIBUTE_REPAIR_MAINTENANCE_RESULT_REVIEW_20260729_v0.json"
)


def _read(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_v4_closes_maintenance_without_scientific_rotation() -> None:
    authority = _read(AUTHORITY_PATH)
    assert authority["status"] == "COMPLETE_ACCEPTED_NO_AUTOMATIC_SUCCESSOR"
    scientific = authority["scientific_authority"]
    assert isinstance(scientific, dict)
    assert scientific["target_rotated"] is False
    assert scientific["current_target"] == (
        "prepare_qft_gr_quadratic_generic_background_linearization_"
        "gauge_and_jet_contract_v0"
    )
    boundary = authority["boundary"]
    assert isinstance(boundary, dict)
    assert boundary["historical_bytes_rewritten"] is False
    assert boundary["automatic_maintenance_successor_authorized"] is False


def test_v4_binds_result_review_and_pointer() -> None:
    authority = _read(AUTHORITY_PATH)
    review_bytes = REVIEW_PATH.read_bytes()
    completion = authority["completion_result_review"]
    assert isinstance(completion, dict)
    assert completion["sha256"] == hashlib.sha256(review_bytes).hexdigest()

    pointer = _read(POINTER_PATH)
    authority_bytes = AUTHORITY_PATH.read_bytes()
    assert pointer["current_authority_path"] == (
        "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v4.json"
    )
    assert pointer["current_authority_sha256"] == hashlib.sha256(
        authority_bytes
    ).hexdigest()
