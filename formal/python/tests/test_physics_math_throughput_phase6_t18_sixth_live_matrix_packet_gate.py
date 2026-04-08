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
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_18_PHASE6_SIXTH_LIVE_MATRIX_PACKET_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t18_sixth_live_matrix_packet_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase6_t18_files_exist() -> None:
    assert PROGRAM_PATH.exists()
    assert DECLARATION_PATH.exists()
    assert CHECKPOINT_PATH.exists()


def test_phase6_t18_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE6_T18_SIXTH_LIVE_MATRIX_PACKET",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T18_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_18_PHASE6_SIXTH_LIVE_MATRIX_PACKET_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T18_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase6_t18_sixth_live_matrix_packet_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T18_GATE_v0: formal/python/tests/test_physics_math_throughput_phase6_t18_sixth_live_matrix_packet_gate.py",
    ]
    missing = [token for token in required if token not in text]
    assert not missing


def test_phase6_t18_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE6_T18_SIXTH_LIVE_MATRIX_PACKET_v0"
    assert payload.get("status") == "PHASE6_T18_SIXTH_LIVE_MATRIX_PACKET_EXECUTED_NONLIVE_NONCLAIM"

    coverage = payload.get("coverage_contract", {})
    assert coverage.get("declared_tranche_count") == 19
    assert len(coverage.get("tranche_ids", [])) == 19

    packet = payload.get("live_matrix_packet", {})
    assert packet.get("execution_live_enabled") is False
    objectives = packet.get("objectives", {})
    assert objectives.get("primary_pillar") == "QM"
    assert objectives.get("primary_seam") == "SEAM_GR_QM"

    promotion = packet.get("promotion_decision", {})
    assert promotion.get("consecutive_green_packets") == 6
    assert promotion.get("required_consecutive_green_packets") == 2
    assert promotion.get("packet7_authorized") is True
    assert promotion.get("scope_escalation_authorized") is True

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("execution_live_enabled") is False
