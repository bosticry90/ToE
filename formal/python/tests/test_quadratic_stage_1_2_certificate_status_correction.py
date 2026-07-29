from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"


def _read(name: str) -> dict:
    return json.loads((RELEASE_ROOT / name).read_text(encoding="utf-8"))


def test_certificate_status_correction_authority_is_nonadvancing() -> None:
    packet = _read(
        "QUADRATIC_STAGE_1_2_CERTIFICATE_STATUS_CORRECTION_AUTHORITY_PACKET_20260729_v0.json"
    )
    review = _read(
        "QUADRATIC_STAGE_1_2_CERTIFICATE_STATUS_CORRECTION_AUTHORITY_PACKET_REVIEW_20260729_v0.json"
    )
    assert packet["status"] == (
        "AUTHORIZED_NONADVANCING_SCIENTIFIC_CUSTODY_CORRECTION_ONLY"
    )
    assert review["status"] == (
        "ACCEPTED_NONADVANCING_SCIENTIFIC_CUSTODY_CORRECTION_AUTHORITY"
    )
    assert packet["scientific_target_preserved"] == (
        "close_toe_native_surrogate_v0_after_bounded_result_v0"
    )
    assert review["scientific_target_preserved"] == packet["scientific_target_preserved"]
    assert packet["preserved_terminal_outcomes"] == {
        "native_surrogate_v0": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        "quadratic_control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        "quadratic_toe_role": "REFERENCE_CONTROL_ONLY",
    }
    prohibitions = "\n".join(packet["prohibitions"])
    assert "No reopening" in prohibitions
    assert "No new bounded-program attempt or repair." in prohibitions
    assert "No executable rewrite-confluence proof." in prohibitions
    assert "No new tensor-identity proof." in prohibitions
