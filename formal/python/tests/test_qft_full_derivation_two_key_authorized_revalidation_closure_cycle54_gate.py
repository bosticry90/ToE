from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle54_two_key_authorized_revalidation_closure_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE54_v0: "
        "TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_GATE_v0: "
        "REQUIRE_KEYA_KEYB_AUTHORIZED_PACKET_AND_POST_AUTH_REVALIDATION_CLOSURE_NONFLIP" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_SCOPE_v0: "
        "KEYA_AUTHORIZED_KEYB_AUTHORIZED_REVALIDATION_REPLAY_CLOSURE_REQUIRED_BEFORE_ANY_FLIP" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_ARTIFACT_v0: "
        "qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_v0" in doc
    )
    assert "formal/output/qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_v0.json" in doc


def test_cycle54_two_key_authorized_revalidation_closure_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE54_v0: TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_GATE_v0: REQUIRE_KEYA_KEYB_AUTHORIZED_PACKET_AND_POST_AUTH_REVALIDATION_CLOSURE_NONFLIP",
        "QFT_FULL_DERIVATION_TWO_KEY_AUTHORIZED_REVALIDATION_CLOSURE_SCOPE_v0: KEYA_AUTHORIZED_KEYB_AUTHORIZED_REVALIDATION_REPLAY_CLOSURE_REQUIRED_BEFORE_ANY_FLIP",
        "formal/python/tests/test_qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_gate.py",
    ]
    for token in required:
        assert token in state
        assert token in roadmap


def test_cycle54_two_key_authorized_revalidation_closure_preserves_nonflip_adjudication_tokens() -> None:
    doc = _read(Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"))
    assert "QFT_FULL_DERIVATION_ADJUDICATION_EXECUTION_GUARD_GATE_v0: FLIP_FORBIDDEN_UNLESS_TWO_KEY_AUTHORIZED_AND_NONPENDING" in doc
    assert "QFT_FULL_DERIVATION_POST_AUTH_REVALIDATION_PACKET_GATE_v0: REVALIDATION_REQUIRED_AFTER_ANY_AUTH_STATUS_CHANGE" in doc
    assert "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED" in doc


def test_cycle54_two_key_authorized_revalidation_closure_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_two_key_authorized_revalidation_closure_cycle54_v0"' in artifact
    assert '"cycle": 54' in artifact
    assert '"status": "two_key_authorized_revalidation_closure_locked"' in artifact
    assert '"key_state_packet": "KEYA_AUTHORIZED_KEYB_AUTHORIZED"' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"adjudication_token_state_verified": "NOT_YET_DISCHARGED"' in artifact
