from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle24_co_notarization_token_chain_and_gate_pointers() -> None:
    repo_root = Path(__file__).resolve().parents[3]

    state = _read(repo_root / "State_of_the_Theory.md")
    target = _read(
        repo_root
        / "formal"
        / "docs"
        / "paper"
        / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
    )
    roadmap = _read(repo_root / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md")

    progress = (
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_NOTARIZATION_PROGRESS_CYCLE24_v0"
    )
    gate = "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_NOTARIZATION_GATE_v0"
    authority_gate = (
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_NOTARIZATION_AUTHORITY_GATE_v0"
    )
    artifact_ref = (
        "formal/output/cosmo_full_discharge_active_mode_changeset_co_notarization_packet_cycle24_v0.json"
    )
    gate_test_ref = (
        "formal/python/tests/test_cosmo_full_derivation_active_mode_changeset_co_notarization_cycle24_gate.py"
    )

    for token in (progress, gate, authority_gate, artifact_ref, gate_test_ref):
        assert token in state
        assert token in target
        assert token in roadmap


def test_cycle24_co_notarization_packet_preserves_blocked_posture() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    packet = _read(
        repo_root
        / "formal"
        / "output"
        / "cosmo_full_discharge_active_mode_changeset_co_notarization_packet_cycle24_v0.json"
    )

    assert (
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_NOTARIZATION_PROGRESS_CYCLE24_v0"
        in packet
    )
    assert "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_NOTARIZATION_GATE_v0" in packet
    assert (
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_NOTARIZATION_AUTHORITY_GATE_v0"
        in packet
    )
    assert "\"can_issue_active_mode_changeset_co_notarization\": false" in packet
    assert "COSMO_BACKGROUND_ADJUDICATION: NOT_YET_DISCHARGED" in packet
    assert "PROCEED_GATE_COSMO: BLOCKED_v0_PHYSICS_NOT_CLOSED" in packet
