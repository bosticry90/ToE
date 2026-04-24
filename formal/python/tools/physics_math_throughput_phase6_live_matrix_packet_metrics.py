from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.physics_math_throughput_rolling_window_metrics import compute_metrics
from formal.python.meta.repo_environment import find_repo_root

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
T14_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t14_second_live_matrix_packet_20260407_v0.json"
)
T15_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t15_third_live_matrix_packet_20260407_v0.json"
)
T16_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t16_fourth_live_matrix_packet_20260407_v0.json"
)
T17_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t17_fifth_live_matrix_packet_20260407_v0.json"
)
T18_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t18_sixth_live_matrix_packet_20260407_v0.json"
)


def _read_json(path: Path) -> dict:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def compute_live_matrix_packet_metrics() -> dict:
    t12 = _read_json(T12_PATH)
    if T18_PATH.exists():
        packet_payload = _read_json(T18_PATH)
    elif T17_PATH.exists():
        packet_payload = _read_json(T17_PATH)
    elif T16_PATH.exists():
        packet_payload = _read_json(T16_PATH)
    elif T15_PATH.exists():
        packet_payload = _read_json(T15_PATH)
    elif T14_PATH.exists():
        packet_payload = _read_json(T14_PATH)
    else:
        packet_payload = _read_json(T13_PATH)
    rolling = compute_metrics()

    delta = t12.get("go_no_go_contract", {}).get("delta_fields", {})
    packet = packet_payload.get("live_matrix_packet", {})
    evidence = packet.get("execution_evidence", {}).get("packet_metrics", {})

    return {
        "packet_status": packet_payload.get("status"),
        "execution_live_enabled": bool(packet.get("execution_live_enabled", False)),
        "primary_pillar": packet.get("objectives", {}).get("primary_pillar", "UNSELECTED"),
        "primary_seam": packet.get("objectives", {}).get("primary_seam", "UNSELECTED"),
        "science_surface_share_delta": float(evidence.get("science_surface_share_delta", delta.get("science_surface_share_delta", 0.0))),
        "theorem_depth_queue_delta": float(evidence.get("theorem_depth_queue_delta", delta.get("theorem_depth_queue_delta", 0.0))),
        "seam_empirical_packet_delta": float(evidence.get("seam_empirical_packet_delta", delta.get("seam_empirical_packet_delta", 0.0))),
        "rolling_science_signal": float(evidence.get("rolling_science_signal", rolling.get("science_signal_rolling_mean", 0.0))),
        "rolling_controls_signal": float(evidence.get("rolling_controls_signal", rolling.get("controls_signal_rolling_mean", 0.0))),
        "authorization_window_hours": int(packet.get("execution_window", {}).get("authorization_window_hours", 0)),
    }


def main() -> int:
    m = compute_live_matrix_packet_metrics()
    print(
        "live_matrix_packet_metrics: "
        f"status={m['packet_status']} "
        f"live_enabled={m['execution_live_enabled']} "
        f"primary_pillar={m['primary_pillar']} "
        f"primary_seam={m['primary_seam']} "
        f"science_roll={m['rolling_science_signal']} "
        f"controls_roll={m['rolling_controls_signal']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
