from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle37_dryrun_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE37_v0: "
        "TOKEN_FLIP_DRYRUN_SIMULATOR_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_GATE_v0: "
        "SIMULATION_ONLY_NO_TOKEN_WRITE" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_SCOPE_v0: "
        "READINESS_CHECK_AGAINST_CYCLE27_36_BUNDLES_ONLY" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_SIMULATOR_ARTIFACT_v0: "
        "qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0" in doc
    )
    assert (
        "formal/output/qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0.json"
        in doc
    )


def test_cycle37_dryrun_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE37_v0: TOKEN_FLIP_DRYRUN_SIMULATOR_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_GATE_v0: SIMULATION_ONLY_NO_TOKEN_WRITE",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_SCOPE_v0: READINESS_CHECK_AGAINST_CYCLE27_36_BUNDLES_ONLY",
        "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_simulator_cycle37_gate.py",
    ]
    for token in required:
        assert token in state
        assert token in roadmap


def test_cycle37_dryrun_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_token_flip_dryrun_simulator_cycle37_v0"' in artifact
    assert '"cycle": 37' in artifact
    assert '"dryrun_mode": "simulation_only"' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"readiness_scope": "cycle27_36_bundles_only"' in artifact
