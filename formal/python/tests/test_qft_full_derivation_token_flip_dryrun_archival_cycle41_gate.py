from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle41_dryrun_archival_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE41_v0: "
        "TOKEN_FLIP_DRYRUN_ARCHIVAL_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_GATE_v0: "
        "REQUIRE_CYCLE40_CLOSURE_AND_IMMUTABLE_ARCHIVE_PIN" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_SCOPE_v0: "
        "CYCLE37_40_TRACE_CHAIN_ARCHIVED_NO_TOKEN_WRITE" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_ARTIFACT_v0: "
        "qft_full_derivation_token_flip_dryrun_archival_cycle41_v0" in doc
    )
    assert "formal/output/qft_full_derivation_token_flip_dryrun_archival_cycle41_v0.json" in doc


def test_cycle41_dryrun_archival_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    inventory = _read(Path("formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE41_v0: TOKEN_FLIP_DRYRUN_ARCHIVAL_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_GATE_v0: REQUIRE_CYCLE40_CLOSURE_AND_IMMUTABLE_ARCHIVE_PIN",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ARCHIVAL_SCOPE_v0: CYCLE37_40_TRACE_CHAIN_ARCHIVED_NO_TOKEN_WRITE",
        "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_archival_cycle41_gate.py",
    ]
    for token in required:
        assert token in state or token in inventory
        assert token in roadmap


def test_cycle41_dryrun_archival_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_token_flip_dryrun_archival_cycle41_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_token_flip_dryrun_archival_cycle41_v0"' in artifact
    assert '"cycle": 41' in artifact
    assert '"status": "archived"' in artifact
    assert '"source_cycles": [37, 38, 39, 40]' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"archive_result": "trace_chain_archived_immutable_nonwrite"' in artifact


