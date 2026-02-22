from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle57_flip_eligibility_attestation_packet_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE57_v0: "
        "FLIP_ELIGIBILITY_ATTESTATION_PACKET_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_FLIP_ELIGIBILITY_ATTESTATION_PACKET_GATE_v0: "
        "REQUIRE_PREFLIP_AUTHORITY_ATTESTATION_PACKET_AND_NONFLIP_GUARD_STILL_ACTIVE" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_FLIP_ELIGIBILITY_ATTESTATION_PACKET_SCOPE_v0: "
        "ELIGIBILITY_ATTESTED_WITHOUT_EXECUTING_OR_AUTHORIZING_ADJUDICATION_FLIP" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_FLIP_ELIGIBILITY_ATTESTATION_PACKET_ARTIFACT_v0: "
        "qft_full_derivation_flip_eligibility_attestation_packet_cycle57_v0" in doc
    )
    assert "formal/output/qft_full_derivation_flip_eligibility_attestation_packet_cycle57_v0.json" in doc


def test_cycle57_flip_eligibility_attestation_packet_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE57_v0: FLIP_ELIGIBILITY_ATTESTATION_PACKET_LOCK_PINNED",
        "QFT_FULL_DERIVATION_FLIP_ELIGIBILITY_ATTESTATION_PACKET_GATE_v0: REQUIRE_PREFLIP_AUTHORITY_ATTESTATION_PACKET_AND_NONFLIP_GUARD_STILL_ACTIVE",
        "QFT_FULL_DERIVATION_FLIP_ELIGIBILITY_ATTESTATION_PACKET_SCOPE_v0: ELIGIBILITY_ATTESTED_WITHOUT_EXECUTING_OR_AUTHORIZING_ADJUDICATION_FLIP",
        "formal/python/tests/test_qft_full_derivation_flip_eligibility_attestation_packet_cycle57_gate.py",
    ]
    for token in required:
        assert token in state
        assert token in roadmap


def test_cycle57_flip_eligibility_attestation_packet_preserves_nonflip_adjudication_tokens() -> None:
    doc = _read(Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"))
    assert "QFT_FULL_DERIVATION_PREFLIP_AUTHORITY_ATTESTATION_PACKET_GATE_v0: REQUIRE_NONFLIP_EXECUTION_READINESS_PACKET_AND_EXPLICIT_PREFLIP_AUTHORITY_ATTESTATION" in doc
    assert "QFT_FULL_DERIVATION_ADJUDICATION_EXECUTION_GUARD_GATE_v0: FLIP_FORBIDDEN_UNLESS_TWO_KEY_AUTHORIZED_AND_NONPENDING" in doc
    assert "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED" in doc


def test_cycle57_flip_eligibility_attestation_packet_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_flip_eligibility_attestation_packet_cycle57_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_flip_eligibility_attestation_packet_cycle57_v0"' in artifact
    assert '"cycle": 57' in artifact
    assert '"status": "flip_eligibility_attestation_packet_locked"' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"adjudication_token_state_verified": "NOT_YET_DISCHARGED"' in artifact
