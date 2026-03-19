from __future__ import annotations

from pathlib import Path


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_cycle40_dryrun_closure_tokens_in_discharge_doc() -> None:
    doc = _read(
        Path("formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md")
    )
    assert (
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE40_v0: "
        "TOKEN_FLIP_DRYRUN_CLOSURE_LOCK_PINNED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_GATE_v0: "
        "REQUIRE_RECONCILIATION_COMPLETE_AND_NONWRITE_FINALIZED" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_SCOPE_v0: "
        "CYCLE39_RECONCILIATION_PLUS_CYCLE37_38_TRACEABILITY" in doc
    )
    assert (
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_ARTIFACT_v0: "
        "qft_full_derivation_token_flip_dryrun_closure_cycle40_v0" in doc
    )
    assert "formal/output/qft_full_derivation_token_flip_dryrun_closure_cycle40_v0.json" in doc


def test_cycle40_dryrun_closure_tokens_in_state_and_roadmap() -> None:
    state = _read(Path("State_of_the_Theory.md"))
    inventory = _read(Path("formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md"))
    roadmap = _read(Path("formal/docs/paper/PHYSICS_ROADMAP_v0.md"))

    required = [
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE40_v0: TOKEN_FLIP_DRYRUN_CLOSURE_LOCK_PINNED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_GATE_v0: REQUIRE_RECONCILIATION_COMPLETE_AND_NONWRITE_FINALIZED",
        "QFT_FULL_DERIVATION_TOKEN_FLIP_DRYRUN_CLOSURE_SCOPE_v0: CYCLE39_RECONCILIATION_PLUS_CYCLE37_38_TRACEABILITY",
        "formal/python/tests/test_qft_full_derivation_token_flip_dryrun_closure_cycle40_gate.py",
    ]
    for token in required:
        assert token in state or token in inventory
        assert token in roadmap


def test_cycle40_dryrun_closure_artifact_json_exists_and_is_consistent() -> None:
    artifact = _read(
        Path(
            "formal/output/"
            "qft_full_derivation_token_flip_dryrun_closure_cycle40_v0.json"
        )
    )
    assert '"artifact_id": "qft_full_derivation_token_flip_dryrun_closure_cycle40_v0"' in artifact
    assert '"cycle": 40' in artifact
    assert '"status": "closure_locked"' in artifact
    assert '"source_cycles": [37, 38, 39]' in artifact
    assert '"token_write_allowed": false' in artifact
    assert '"closure_result": "dryrun_lane_closed_no_mutation"' in artifact


