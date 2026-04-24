from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase6_non_placeholder_delta_gate_token_present() -> None:
    text = _read(PROGRAM_PATH)
    token = (
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_NON_PLACEHOLDER_DELTA_GATE_v0: "
        "formal/python/tests/test_physics_math_throughput_phase6_non_placeholder_delta_gate.py"
    )
    assert token in text


def test_phase6_delta_fields_are_non_placeholder() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    delta = payload.get("go_no_go_contract", {}).get("delta_fields", {})

    assert isinstance(delta.get("science_surface_share_delta"), (float, int))
    assert isinstance(delta.get("theorem_depth_queue_delta"), int)
    assert isinstance(delta.get("seam_empirical_packet_delta"), int)
    assert isinstance(delta.get("controls_overhead_delta"), (float, int))

    assert delta.get("science_surface_share_delta") != 0.0
    assert delta.get("theorem_depth_queue_delta") != 0
    assert delta.get("seam_empirical_packet_delta") != 0
    assert delta.get("controls_overhead_delta") != 0.0


def test_phase6_delta_signal_policy() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    delta = payload.get("go_no_go_contract", {}).get("delta_fields", {})

    signal_flags = [
        delta.get("science_surface_share_delta", 0.0) > 0,
        delta.get("theorem_depth_queue_delta", 0) > 0,
        delta.get("seam_empirical_packet_delta", 0) > 0,
    ]
    assert sum(signal_flags) >= 2


def test_phase6_delta_provenance_present() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    provenance = payload.get("go_no_go_contract", {}).get("delta_provenance", {})
    assert provenance.get("refresh_tool") == "formal/python/tools/physics_math_throughput_phase6_delta_refresh.py"
    assert provenance.get("method") == "proxy_from_baseline_and_execution_packets"
