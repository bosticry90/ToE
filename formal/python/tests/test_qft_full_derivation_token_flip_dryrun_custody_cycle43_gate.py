from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle43_dryrun_custody_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE43_v0: "
        "TOKEN_FLIP_DRYRUN_CUSTODY_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_GATE_v0: "
        "REQUIRE_HANDOFF_COMPLETENESS_AND_CUSTODY_CHAIN_SEAL" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_SCOPE_v0: "
        "CYCLE42_HANDOFF_WITH_CYCLE37_41_AUDIT_LINKAGE" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_ARTIFACT_v0: "
        "qft_full_derivation_token_flip_dryrun_custody_cycle43_v0" in doc
    )
    assert "formal/output/qft_full_derivation_token_flip_dryrun_custody_cycle43_v0.json" in doc


def test_cycle43_dryrun_custody_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE43_v0: TOKEN_FLIP_DRYRUN_CUSTODY_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_GATE_v0: REQUIRE_HANDOFF_COMPLETENESS_AND_CUSTODY_CHAIN_SEAL",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CUSTODY_SCOPE_v0: CYCLE42_HANDOFF_WITH_CYCLE37_41_AUDIT_LINKAGE",
        "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_custody_cycle43_gate.py",
    ]
    for token in required:
        assert token in state
        assert token in roadmap


def test_cycle43_dryrun_custody_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_token_flip_dryrun_custody_cycle43_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_token_flip_dryrun_custody_cycle43_v0"' in artifact
    assert '"cycle": 43' in artifact
    assert '"status": "custody_sealed"' in artifact
    assert '"source_cycles": [37, 38, 39, 40, 41, 42]' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"custody_result": "handoff_chain_sealed_nonwrite"' in artifact
