from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle42_dryrun_handoff_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE42_v0: "
        "TOKEN_FLIP_DRYRUN_HANDOFF_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_GATE_v0: "
        "REQUIRE_ARCHIVAL_IMMUTABILITY_AND_HANDOFF_READINESS" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_SCOPE_v0: "
        "CYCLE41_ARCHIVE_CHAIN_AND_CYCLE37_40_TRACE_TRANSFER" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_ARTIFACT_v0: "
        "qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0" in doc
    )
    assert "formal/output/qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0.json" in doc


def test_cycle42_dryrun_handoff_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    inventory = _read(Path("formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE42_v0: TOKEN_FLIP_DRYRUN_HANDOFF_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_GATE_v0: REQUIRE_ARCHIVAL_IMMUTABILITY_AND_HANDOFF_READINESS",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_HANDOFF_SCOPE_v0: CYCLE41_ARCHIVE_CHAIN_AND_CYCLE37_40_TRACE_TRANSFER",
        "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_handoff_cycle42_gate.py",
    ]
    for token in required:
        assert token in state or token in inventory
        assert token in roadmap


def test_cycle42_dryrun_handoff_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_token_flip_dryrun_handoff_cycle42_v0"' in artifact
    assert '"cycle": 42' in artifact
    assert '"status": "handoff_ready"' in artifact
    assert '"source_cycles": [37, 38, 39, 40, 41]' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"handoff_result": "archive_chain_handoff_ready_nonwrite"' in artifact




