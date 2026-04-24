from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PACKET_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "proof_debt_burndown_checkpoint_cycle05_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_COMPLETE_V1_PROGRAM_v0.md"

PACKET_REL = "formal/docs/release/PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0.md"
CHECKPOINT_REL = "formal/output/proof_debt_burndown_checkpoint_cycle05_v0.json"
TRACKED_KEYS = {
    "gapid_COMP-FN-REP-GRID",
    "gapid_COMP-FN-REP-NONALIAS-EQUIV-01",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_proof_debt_cycle05_packet_and_checkpoint_are_pinned() -> None:
    packet_text = _read(PACKET_PATH)
    checkpoint_payload = json.loads(_read(CHECKPOINT_PATH))

    for token in (
        "PROOF_DEBT_BURNDOWN_PACKET_CYCLE05_v0",
        "PROOF_DEBT_BURNDOWN_TARGET_01_v0: GAPID_STABILITY_RECONFIRMATION_CHAIN",
        "PROOF_DEBT_BURNDOWN_TARGET_02_v0: REGRESSION_ONLY_REOPEN_POSTURE_RECONFIRMATION_CHAIN",
        "PROOF_DEBT_BURNDOWN_CONTINUITY_MODE_v0: POST_CLOSEOUT_REGRESSION_MONITORING",
        CHECKPOINT_REL,
    ):
        assert token in packet_text

    assert checkpoint_payload["checkpoint_id"] == "PROOF_DEBT_BURNDOWN_CHECKPOINT_CYCLE05_v0"
    assert checkpoint_payload["status"] == "CONTINUITY_AUDIT_EXECUTED_v0_NONCLAIM"
    assert checkpoint_payload["mode"] == "PARALLEL_BOUNDED_NONCLAIM"
    assert checkpoint_payload["status_summary"]["critical_pending_tokens_remaining"] == 0
    assert set(checkpoint_payload["target_markers"]) == TRACKED_KEYS


def test_proof_debt_cycle05_cross_surface_pointer_parity() -> None:
    refs = (PACKET_REL, CHECKPOINT_REL)

    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)
    program_text = _read(PROGRAM_PATH)

    for ref in refs:
        assert ref in roadmap_text
        assert ref in program_text
        assert ref in state_text or ref in inventory_text
