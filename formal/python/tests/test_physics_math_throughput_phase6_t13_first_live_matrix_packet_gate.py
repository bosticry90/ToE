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
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_13_PHASE6_FIRST_LIVE_MATRIX_PACKET_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase6_t13_files_exist() -> None:
    assert PROGRAM_PATH.exists()
    assert DECLARATION_PATH.exists()
    assert CHECKPOINT_PATH.exists()


def test_phase6_t13_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE6_T13_FIRST_LIVE_MATRIX_PACKET_PREEXECUTION",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T13_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_13_PHASE6_FIRST_LIVE_MATRIX_PACKET_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T13_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_T13_GATE_v0: formal/python/tests/test_physics_math_throughput_phase6_t13_first_live_matrix_packet_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_MATRIX_OBJECTIVE_GATE_v0: formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_LIVE_EXPIRY_GATE_v0: formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_LIVE_INVARIANCE_CONTINUITY_GATE_v0: formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_PROMOTION_POLICY_GATE_v0: formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_MATRIX_MODE_v0: ONE_PRIMARY_PILLAR_PLUS_ONE_PRIMARY_SEAM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_NON_SELECTED_LANES_POLICY_v0: EXPLICIT_PAUSED_STATUS_REQUIRED",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_LIVE_AUTHORIZATION_EXPIRY_v0: 72_HOURS",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_PROMOTION_POLICY_v0: CONSERVATIVE_TWO_CONSECUTIVE_GREEN_LIVE_PACKETS_REQUIRED",
    ]
    missing = [token for token in required if token not in text]
    assert not missing


def test_phase6_t13_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE6_T13_FIRST_LIVE_MATRIX_PACKET_v0"
    assert payload.get("status") == "PHASE6_T13_FIRST_LIVE_MATRIX_PACKET_EXECUTED_NONLIVE_NONCLAIM"

    coverage = payload.get("coverage_contract", {})
    assert coverage.get("declared_tranche_count") == 14
    assert len(coverage.get("tranche_ids", [])) == 14

    packet = payload.get("live_matrix_packet", {})
    assert packet.get("execution_mode") == "ONE_PRIMARY_PILLAR_PLUS_ONE_PRIMARY_SEAM"
    assert packet.get("execution_live_enabled") is False

    window = packet.get("execution_window", {})
    assert window.get("authorization_window_hours") == 72
    assert window.get("window_state") == "EXECUTION_COMPLETED_NONLIVE"

    objectives = packet.get("objectives", {})
    assert objectives.get("primary_pillar") == "QM"
    assert objectives.get("primary_seam") == "SEAM_GR_QM"
    assert objectives.get("lane_selection_required_before_execution") is True

    lane_status = packet.get("lane_status", {})
    assert lane_status
    assert lane_status.get("QM") == "SELECTED_EXECUTED_NONLIVE"
    assert lane_status.get("SEAM_GR_QM") == "SELECTED_EXECUTED_NONLIVE"

    required_green = set(packet.get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_t13_first_live_matrix_packet_gate.py" in required_green
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_matrix_objective_gate.py" in required_green
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_authorization_expiry_gate.py" in required_green
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_invariance_continuity_gate.py" in required_green
    assert "formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py" in required_green

    measurement = packet.get("measurement_wiring", {})
    assert measurement.get("delta_refresh_tool") == "formal/python/tools/physics_math_throughput_phase6_delta_refresh.py"
    assert measurement.get("rolling_window_tool") == "formal/python/tools/physics_math_throughput_rolling_window_metrics.py"
    assert measurement.get("live_matrix_packet_metrics_tool") == (
        "formal/python/tools/physics_math_throughput_phase6_live_matrix_packet_metrics.py"
    )

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("execution_live_enabled") is False
