from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle39_dryrun_reconciliation_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE39_v0: "
        "TOKEN_FLIP_DRYRUN_RECONCILIATION_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_GATE_v0: "
        "REQUIRE_ATTESTATION_MATCH_AND_NO_TOKEN_MUTATION" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_SCOPE_v0: "
        "CYCLE38_ATTESTATION_AND_CYCLE37_SIMULATOR_ALIGNMENT" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_ARTIFACT_v0: "
        "qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0" in doc
    )
    assert (
        "formal/output/qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0.json"
        in doc
    )


def test_cycle39_dryrun_reconciliation_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE39_v0: TOKEN_FLIP_DRYRUN_RECONCILIATION_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_GATE_v0: REQUIRE_ATTESTATION_MATCH_AND_NO_TOKEN_MUTATION",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_RECONCILIATION_SCOPE_v0: CYCLE38_ATTESTATION_AND_CYCLE37_SIMULATOR_ALIGNMENT",
        "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_gate.py",
    ]
    for token in required:
        assert token in state
        assert token in roadmap


def test_cycle39_dryrun_reconciliation_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0.json"
        )
    )
    assert (
        '"artifact_id": "qft_full_derivation_token_flip_dryrun_reconciliation_cycle39_v0"'
        in artifact
    )
    assert '"cycle": 39' in artifact
    assert '"status": "reconciled"' in artifact
    assert '"source_cycles": [37, 38]' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"reconciliation_result": "attestation_matches_simulator_no_mutation"' in artifact
