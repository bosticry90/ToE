from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"


def _read(name: str) -> dict:
    return json.loads((RELEASE_ROOT / name).read_text(encoding="utf-8"))


def test_governance_enforcement_completion_is_maintenance_only() -> None:
    packet = _read(
        "BOUNDED_PROGRAM_GOVERNANCE_ENFORCEMENT_COMPLETION_MAINTENANCE_PACKET_20260729_v0.json"
    )
    review = _read(
        "BOUNDED_PROGRAM_GOVERNANCE_ENFORCEMENT_COMPLETION_MAINTENANCE_PACKET_REVIEW_20260729_v0.json"
    )
    assert packet["status"] == "AUTHORIZED_MAINTENANCE_ONLY"
    assert review["status"] == "ACCEPTED_MAINTENANCE_AUTHORIZATION_ONLY"
    assert packet["scientific_target_preserved"] == (
        "close_toe_native_surrogate_v0_after_bounded_result_v0"
    )
    assert review["scientific_target_preserved"] == packet["scientific_target_preserved"]
    assert packet["preserved_terminal_outcomes"] == {
        "native_surrogate_v0": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        "quadratic_control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        "quadratic_toe_role": "REFERENCE_CONTROL_ONLY",
    }
    assert all(packet["authorized_scope"].values())
    prohibitions = "\n".join(packet["prohibitions"])
    assert "No scientific target rotation." in prohibitions
    assert "No reopening" in prohibitions
    assert "No original OPEN, CLOSE, calculation, or review artifact rewrite." in prohibitions


def test_governance_enforcement_completion_result_preserves_outcomes() -> None:
    result = _read(
        "BOUNDED_PROGRAM_GOVERNANCE_ENFORCEMENT_COMPLETION_MAINTENANCE_RESULT_REVIEW_20260729_v0.json"
    )
    assert result["accepted"] is True
    assert result["status"] == (
        "ACCEPTED_GOVERNANCE_ENFORCEMENT_COMPLETE_NO_SCIENTIFIC_ROTATION"
    )
    assert result["implemented_controls"]["immutable_manifest_count"] == 2
    assert result["implemented_controls"]["historical_event_bytes_verified_immutable"] == 8
    assert result["implemented_controls"]["adversarial_mutations_fail_for_intended_reasons"] == 25
    assert result["preserved_outcomes"] == {
        "native_surrogate_terminal": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        "quadratic_control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        "quadratic_toe_role": "REFERENCE_CONTROL_ONLY",
    }
