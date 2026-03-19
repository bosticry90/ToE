from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle59_preexecution_nonflip_execution_boundary_packet_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE59_v0: "
        "PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_GATE_v0: "
        "REQUIRE_FINAL_PREEXECUTION_NONFLIP_ATTESTATION_PACKET_AND_EXECUTION_BOUNDARY_NONFLIP_CONFIRMATION" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_SCOPE_v0: "
        "PREEXECUTION_BOUNDARY_CONFIRMATION_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_ARTIFACT_v0: "
        "qft_full_derivation_preexecution_nonflip_execution_boundary_packet_cycle59_v0" in doc
    )
    assert (
        "formal/output/"
        "qft_full_derivation_preexecution_nonflip_execution_boundary_packet_cycle59_v0.json" in doc
    )


def test_cycle59_preexecution_nonflip_execution_boundary_packet_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    inventory = _read(Path("formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE59_v0: PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_LOCK_PINNED",
        "QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_GATE_v0: REQUIRE_FINAL_PREEXECUTION_NONFLIP_ATTESTATION_PACKET_AND_EXECUTION_BOUNDARY_NONFLIP_CONFIRMATION",
        "QFT_FULL_DERIVATION_PREEXECUTION_NONFLIP_EXECUTION_BOUNDARY_PACKET_SCOPE_v0: PREEXECUTION_BOUNDARY_CONFIRMATION_MAINTAINS_NONFLIP_EXECUTION_AND_NO_ADJUDICATION_FLIP",
        "formal/python/tests/test_qft_full_derivation_preexecution_nonflip_execution_boundary_packet_cycle59_gate.py",
    ]
    for token in required:
        assert token in state or token in inventory
        assert token in roadmap


def test_cycle59_preexecution_nonflip_execution_boundary_packet_preserves_nonflip_adjudication_tokens() -> None:
    doc = _read(Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"))
    assert "QFT_FULL_DERIVATION_FINAL_PREEXECUTION_NONFLIP_ATTESTATION_PACKET_GATE_v0: REQUIRE_FLIP_ELIGIBILITY_ATTESTATION_PACKET_AND_FINAL_PREEXECUTION_NONFLIP_ATTESTATION" in doc
    assert "QFT_FULL_DERIVATION_ADJUDICATION_EXECUTION_GUARD_GATE_v0: FLIP_FORBIDDEN_UNLESS_TWO_KEY_AUTHORIZED_AND_NONPENDING" in doc
    assert "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED" in doc


def test_cycle59_preexecution_nonflip_execution_boundary_packet_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_preexecution_nonflip_execution_boundary_packet_cycle59_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_preexecution_nonflip_execution_boundary_packet_cycle59_v0"' in artifact
    assert '"cycle": 59' in artifact
    assert '"status": "preexecution_nonflip_execution_boundary_packet_locked"' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"adjudication_token_state_verified": "NOT_YET_DISCHARGED"' in artifact




