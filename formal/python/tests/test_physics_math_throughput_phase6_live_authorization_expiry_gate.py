from __future__ import annotations

import json
from datetime import datetime
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _parse_utc(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def test_live_expiry_window_is_fixed_to_72_hours() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    window = payload.get("live_matrix_packet", {}).get("execution_window", {})
    assert window.get("authorization_window_hours") == 72


def test_non_live_preexecution_has_not_started_window() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    packet = payload.get("live_matrix_packet", {})
    window = packet.get("execution_window", {})

    if packet.get("execution_live_enabled") is False and window.get("window_state") == "NOT_STARTED":
        assert window.get("window_state") == "NOT_STARTED"
        assert window.get("window_start_utc") is None
        assert window.get("window_expiry_utc") is None


def test_non_live_executed_window_has_timestamps() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    packet = payload.get("live_matrix_packet", {})
    window = packet.get("execution_window", {})

    if packet.get("execution_live_enabled") is False and window.get("window_state") == "EXECUTION_COMPLETED_NONLIVE":
        assert isinstance(window.get("window_start_utc"), str)
        assert isinstance(window.get("window_expiry_utc"), str)


def test_live_window_timestamps_are_ordered_when_present() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    packet = payload.get("live_matrix_packet", {})
    window = packet.get("execution_window", {})
    start = window.get("window_start_utc")
    expiry = window.get("window_expiry_utc")

    if start and expiry:
        assert _parse_utc(expiry) > _parse_utc(start)
