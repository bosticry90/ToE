from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle38_dryrun_attestation_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE38_v0: "
        "TOKEN_FLIP_DRYRUN_ATTESTATION_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_GATE_v0: "
        "REQUIRE_SIMULATOR_OUTPUT_AND_NONWRITE_CONFIRMATION" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_SCOPE_v0: "
        "CYCLE37_SIMULATOR_AND_CYCLE27_36_INPUTS_REPLAYED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_ARTIFACT_v0: "
        "qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0" in doc
    )
    assert (
        "formal/output/qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0.json"
        in doc
    )


def test_cycle38_dryrun_attestation_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE38_v0: TOKEN_FLIP_DRYRUN_ATTESTATION_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_GATE_v0: REQUIRE_SIMULATOR_OUTPUT_AND_NONWRITE_CONFIRMATION",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_ATTESTATION_SCOPE_v0: CYCLE37_SIMULATOR_AND_CYCLE27_36_INPUTS_REPLAYED",
        "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_attestation_cycle38_gate.py",
    ]
    for token in required:
        assert token in state
        assert token in roadmap


def test_cycle38_dryrun_attestation_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0.json"
        )
    )
    assert (
        '"artifact_id": "qft_full_derivation_token_flip_dryrun_attestation_cycle38_v0"'
        in artifact
    )
    assert '"cycle": 38' in artifact
    assert '"status": "attested"' in artifact
    assert '"source_cycle": 37' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"readiness_scope": "cycle37_simulator_and_cycle27_36_inputs_replayed"' in artifact
