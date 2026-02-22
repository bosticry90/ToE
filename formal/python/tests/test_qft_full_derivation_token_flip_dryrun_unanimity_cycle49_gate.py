from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle49_dryrun_unanimity_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE49_v0: "
        "TOKEN_FLIP_DRYRUN_UNANIMITY_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_GATE_v0: "
        "REQUIRE_CONSENSUS_COMPLETION_AND_UNANIMOUS_NONWRITE_CONFIRMATION" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_SCOPE_v0: "
        "CYCLE48_CONSENSUS_WITH_CYCLE37_47_CHAIN_REVIEW" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_ARTIFACT_v0: "
        "qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0" in doc
    )
    assert "formal/output/qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0.json" in doc


def test_cycle49_dryrun_unanimity_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE49_v0: TOKEN_FLIP_DRYRUN_UNANIMITY_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_GATE_v0: REQUIRE_CONSENSUS_COMPLETION_AND_UNANIMOUS_NONWRITE_CONFIRMATION",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_UNANIMITY_SCOPE_v0: CYCLE48_CONSENSUS_WITH_CYCLE37_47_CHAIN_REVIEW",
        "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_unanimity_cycle49_gate.py",
    ]
    for token in required:
        assert token in state
        assert token in roadmap


def test_cycle49_dryrun_unanimity_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_token_flip_dryrun_unanimity_cycle49_v0"' in artifact
    assert '"cycle": 49' in artifact
    assert '"status": "unanimous"' in artifact
    assert '"source_cycles": [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"unanimity_result": "consensus_chain_unanimous_nonwrite"' in artifact
