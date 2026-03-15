from __future__ import annotations

import json
from pathlib import Path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_repo_status_audit_checkpoint_core_tokens() -> None:
    root = _repo_root()
    checkpoint_path = root / "formal/output/repo_status_audit_20260315_checkpoint_v0.json"
    payload = _read_json(checkpoint_path)

    assert payload["checkpoint_id"] == "repo_status_audit_20260315_checkpoint_v0"
    assert payload["status"] == "ACTIVE_v0_NONCLAIM"

    tokens = payload["status_tokens"]
    assert tokens["REPO_STATUS_AUDIT_DATE_v0"] == "2026-03-15"
    assert tokens["REPO_STATUS_TOE_COMPLETE_V1_v0"] == "TERMINAL_SATISFIED_v0_NONCLAIM"
    assert tokens["REPO_STATUS_SEAM_PHYSICS_COMPLETE_GLOBAL_v0"] == "NO"
    assert tokens["REPO_STATUS_PACKET41_v0"] == "HOLD_RETAINED_MISSING_NUMERIC_INPUTS"


def test_repo_status_audit_cross_surface_bindings_exist() -> None:
    root = _repo_root()
    checkpoint_path = root / "formal/output/repo_status_audit_20260315_checkpoint_v0.json"
    payload = _read_json(checkpoint_path)

    bindings = payload["bindings"]
    for rel_path in bindings.values():
        assert (root / rel_path).exists(), f"Missing binding target: {rel_path}"


def test_repo_status_audit_parity_in_state_and_roadmap() -> None:
    root = _repo_root()
    state = _read_text(root / "State_of_the_Theory.md")
    roadmap = _read_text(root / "formal/docs/paper/PHYSICS_ROADMAP_v0.md")

    required_lines = [
        "REPO_STATUS_AUDIT_DATE_v0: 2026-03-15",
        "REPO_STATUS_GOVERNANCE_v0: STRONG_BOUNDED_NONCLAIM",
        "REPO_STATUS_PHYSICS_v0: DISCRIMINATIVE_MIXED_PROGRESS",
        "REPO_STATUS_TOE_COMPLETE_V1_v0: TERMINAL_SATISFIED_v0_NONCLAIM",
        "REPO_STATUS_SEAM_PHYSICS_COMPLETE_GLOBAL_v0: NO",
        "REPO_STATUS_PACKET41_v0: HOLD_RETAINED_MISSING_NUMERIC_INPUTS",
        "REPO_STATUS_SCALAR_SUBMISSION_v0: READY_FOR_BOUNDED_PAPER1_SUBMISSION_PACKAGE",
        "formal/docs/release/REPO_STATUS_AUDIT_20260315_v0.md",
        "formal/output/repo_status_audit_20260315_checkpoint_v0.json",
        "formal/python/tests/test_repo_status_audit_20260315_gate.py",
    ]

    for line in required_lines:
        assert line in state, f"Missing state marker: {line}"
        assert line in roadmap, f"Missing roadmap marker: {line}"
