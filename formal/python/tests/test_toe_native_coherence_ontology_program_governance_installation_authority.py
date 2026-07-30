from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"


def _read(name: str) -> dict:
    return json.loads((RELEASE_ROOT / name).read_text(encoding="utf-8"))


def test_coherence_program_installation_is_maintenance_only_and_unopened() -> None:
    packet = _read(
        "TOE_NATIVE_COHERENCE_ONTOLOGY_PROGRAM_GOVERNANCE_INSTALLATION_MAINTENANCE_PACKET_20260729_v0.json"
    )
    review = _read(
        "TOE_NATIVE_COHERENCE_ONTOLOGY_PROGRAM_GOVERNANCE_INSTALLATION_MAINTENANCE_PACKET_REVIEW_20260729_v0.json"
    )
    assert packet["status"] == (
        "AUTHORIZED_MAINTENANCE_INSTALLATION_ONLY_NO_SCIENTIFIC_OPEN"
    )
    assert review["status"] == "ACCEPTED_MAINTENANCE_AUTHORIZATION_ONLY"
    assert packet["program_installation_state_authorized"] == "UNOPENED"
    assert review["program_installation_state_authorized"] == "UNOPENED"
    assert review["consumed_artifact"] == packet["artifact_id"]
    assert review["program_id"] == packet["program_id"]
    assert packet["preserved_scientific_target"] == (
        "prepare_toe_native_coherence_ontology_and_representation_bounded_program_v0"
    )
    assert review["scientific_target_preserved"] == packet["preserved_scientific_target"]
    assert all(packet["authorized_scope"].values())


def test_coherence_program_installation_does_not_authorize_science() -> None:
    packet = _read(
        "TOE_NATIVE_COHERENCE_ONTOLOGY_PROGRAM_GOVERNANCE_INSTALLATION_MAINTENANCE_PACKET_20260729_v0.json"
    )
    prohibitions = "\n".join(packet["prohibitions"])
    assert "No scientific target rotation." in prohibitions
    assert "No Stage 1 OPEN event." in prohibitions
    assert "No claim inventory or other substantive scientific output." in prohibitions
    assert "No modification of the untracked reddit/ directory." in prohibitions
