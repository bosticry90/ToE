from __future__ import annotations

import json
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

PILLAR_LANES = {"QM", "GR", "STAT", "COSMO", "EM", "QFT", "SR"}
SEAM_LANES = {"SEAM_GR_QM", "SEAM_EM_QFT", "SEAM_QM_STAT", "SEAM_COSMO_SR"}


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def test_matrix_objective_fields_are_present() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    objectives = payload.get("live_matrix_packet", {}).get("objectives", {})
    assert "primary_pillar" in objectives
    assert "primary_seam" in objectives
    assert objectives.get("lane_selection_required_before_execution") is True


def test_exactly_one_selected_lane_when_live_enabled_otherwise_unselected() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    packet = payload.get("live_matrix_packet", {})
    objectives = packet.get("objectives", {})

    primary_pillar = objectives.get("primary_pillar")
    primary_seam = objectives.get("primary_seam")

    window_state = packet.get("execution_window", {}).get("window_state")

    if packet.get("execution_live_enabled") is True or window_state in {
        "READY_FOR_EXECUTION",
        "EXECUTION_COMPLETED_NONLIVE",
    }:
        assert primary_pillar in PILLAR_LANES
        assert primary_seam in SEAM_LANES
    else:
        assert primary_pillar == "UNSELECTED"
        assert primary_seam == "UNSELECTED"


def test_non_selected_lanes_are_explicit_and_paused() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    packet = payload.get("live_matrix_packet", {})
    objectives = packet.get("objectives", {})
    lane_status = packet.get("lane_status", {})

    assert PILLAR_LANES.issubset(set(lane_status.keys()))
    assert SEAM_LANES.issubset(set(lane_status.keys()))

    selected_pillar = objectives.get("primary_pillar")
    selected_seam = objectives.get("primary_seam")
    selected_state = packet.get("execution_live_enabled") is True or packet.get("execution_window", {}).get("window_state") in {
        "READY_FOR_EXECUTION",
        "EXECUTION_COMPLETED_NONLIVE",
    }

    for lane in PILLAR_LANES:
        if selected_state and lane == selected_pillar:
            continue
        assert lane_status[lane].startswith("PAUSED")

    for lane in SEAM_LANES:
        if selected_state and lane == selected_seam:
            continue
        assert lane_status[lane].startswith("PAUSED")
