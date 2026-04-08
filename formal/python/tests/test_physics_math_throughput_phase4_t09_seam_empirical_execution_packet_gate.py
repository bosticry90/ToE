from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_09_PHASE4_SEAM_EMPIRICAL_EXECUTION_PACKET_20260407_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase4_t09_seam_empirical_execution_packet_20260407_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase4_t09_files_exist() -> None:
    assert PROGRAM_PATH.exists()
    assert DECLARATION_PATH.exists()
    assert CHECKPOINT_PATH.exists()


def test_phase4_t09_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE4_T09_SEAM_EMPIRICAL_EXECUTION_PACKET",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_T09_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_09_PHASE4_SEAM_EMPIRICAL_EXECUTION_PACKET_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_T09_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase4_t09_seam_empirical_execution_packet_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_T09_GATE_v0: formal/python/tests/test_physics_math_throughput_phase4_t09_seam_empirical_execution_packet_gate.py",
    ]
    missing = [token for token in required if token not in text]
    assert not missing


def test_phase4_t09_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE4_T09_SEAM_EMPIRICAL_EXECUTION_PACKET_v0"
    assert payload.get("status") == "PHASE4_T09_EXECUTION_PACKET_DECLARED_NONLIVE_NONCLAIM"

    packet = payload.get("execution_packet", {})
    assert packet.get("packet_mode") == "BOUNDED_SEAM_AND_PACKET_EXECUTION_PACKET"
    rows = packet.get("rows", [])
    assert len(rows) == 3
    for row in rows:
        assert row.get("target_surface")
        assert row.get("execution_state") == "QUEUED_NONLIVE"


def test_phase4_t09_controls() -> None:
    controls = _read_json(CHECKPOINT_PATH).get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("execution_live_enabled") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_SEAM_PACKET_SCOPE_DRIFT"
