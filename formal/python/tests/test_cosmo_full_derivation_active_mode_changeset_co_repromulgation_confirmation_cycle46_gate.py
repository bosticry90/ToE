from __future__ import annotations

import hashlib
import json
from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cycle46_confirmation_cross_surface_parity_tokens_and_pointers() -> None:
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

    progress = "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_REPROMULGATION_CONFIRMATION_PROGRESS_CYCLE46_v0"
    gate = "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_REPROMULGATION_CONFIRMATION_GATE_v0"
    authority_gate = (
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_REPROMULGATION_CONFIRMATION_AUTHORITY_GATE_v0"
    )
    nonflip_guard = (
        "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_REPROMULGATION_CONFIRMATION_NONFLIP_GUARD_v0"
    )
    artifact_ref = (
        "formal/output/cosmo_full_discharge_active_mode_changeset_co_repromulgation_confirmation_packet_cycle46_v0.json"
    )
    gate_test_ref = (
        "formal/python/tests/test_cosmo_full_derivation_active_mode_changeset_co_repromulgation_confirmation_cycle46_gate.py"
    )
    lane_gate_ref = "formal/python/tests/test_cosmo_full_derivation_discharge_lane_gate.py"
    rollup_crosspin_gate_ref = "formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py"

    for token in (
        progress,
        gate,
        authority_gate,
        nonflip_guard,
        artifact_ref,
        gate_test_ref,
        lane_gate_ref,
        rollup_crosspin_gate_ref,
    ):
        assert token in state
        assert token in target
        assert token in roadmap


def test_cycle46_confirmation_packet_pointer_integrity_to_cycle45() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    packet_path = (
        repo_root
        / "formal"
        / "output"
        / "cosmo_full_discharge_active_mode_changeset_co_repromulgation_confirmation_packet_cycle46_v0.json"
    )
    cycle45_path = (
        repo_root
        / "formal"
        / "output"
        / "cosmo_full_discharge_active_mode_changeset_co_repromulgation_packet_cycle45_v0.json"
    )

    packet = _read_json(packet_path)
    pointer = packet["input_pointer"]

    assert pointer["upstream_artifact_path"] == (
        "formal/output/cosmo_full_discharge_active_mode_changeset_co_repromulgation_packet_cycle45_v0.json"
    )
    assert (
        pointer["upstream_record_id"]
        == "COSMO_FULL_DISCHARGE_ACTIVE_MODE_CHANGESET_CO_REPROMULGATION_PACKET_CYCLE45_v0"
    )

    expected_sha = hashlib.sha256(cycle45_path.read_bytes()).hexdigest().upper()
    assert pointer["upstream_sha256"] == expected_sha


def test_cycle46_confirmation_nonflip_guard_rejects_status_flip_and_comparator_authorization() -> None:
    repo_root = Path(__file__).resolve().parents[3]

    matrix = _read_json(
        repo_root / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
    )
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO", {})
    packet = _read(
        repo_root
        / "formal"
        / "output"
        / "cosmo_full_discharge_active_mode_changeset_co_repromulgation_confirmation_packet_cycle46_v0.json"
    )

    assert cosmo.get("matrix_status") == "CLOSED"
    assert cosmo.get("full_derivation") == "DISCHARGED_v0_BOUNDED"
    assert cosmo.get("inevitability") == "DISCHARGED_v0_BOUNDED"

    assert "\"matrix_status\": \"LOCKED\"" in packet
    assert "\"full_derivation\": \"NOT_YET_DISCHARGED\"" in packet
    assert "\"inevitability\": \"NOT_YET_DISCHARGED\"" in packet
    assert "\"comparator_authorization\": \"NOT_AUTHORIZED\"" in packet
    assert (
        "\"can_issue_active_mode_changeset_co_repromulgation_confirmation\": false"
        in packet
    )
