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
T12_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json"
)
T13_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def test_t13_preserves_invariance_flags_from_t12() -> None:
    t12 = _read_json(T12_PATH)
    t13 = _read_json(T13_PATH)
    t12_controls = t12.get("controls", {})
    t13_controls = t13.get("controls", {})

    keys = [
        "release_gate_truth_changed",
        "nonclaim_boundary_changed",
        "packet_policy_changed",
        "scalar_freeze_policy_changed",
    ]
    for key in keys:
        assert t12_controls.get(key) is False
        assert t13_controls.get(key) is False


def test_t13_remains_nonlive_nonclaim() -> None:
    t13 = _read_json(T13_PATH)
    assert t13.get("status") == "PHASE6_T13_FIRST_LIVE_MATRIX_PACKET_EXECUTED_NONLIVE_NONCLAIM"

    packet = t13.get("live_matrix_packet", {})
    controls = t13.get("controls", {})
    assert packet.get("execution_live_enabled") is False
    assert controls.get("execution_live_enabled") is False


def test_t13_stop_condition_is_live_packet_scope_halt() -> None:
    t13 = _read_json(T13_PATH)
    controls = t13.get("controls", {})
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_LIVE_PACKET_SCOPE_DRIFT"
