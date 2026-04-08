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
T08_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase3_t08_theorem_depth_execution_packet_20260407_v0.json"
T09_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase4_t09_seam_empirical_execution_packet_20260407_v0.json"
T12_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json"
T13_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json"
T14_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase6_t14_second_live_matrix_packet_20260407_v0.json"


def _read_json(path: Path) -> dict:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def rolling_mean(values: list[float]) -> float:
    if not values:
        return 0.0
    return sum(values) / len(values)


def compute_metrics() -> dict:
    t08 = _read_json(T08_PATH)
    t09 = _read_json(T09_PATH)
    t12 = _read_json(T12_PATH)
    t13 = _read_json(T13_PATH)

    t08_science_rows = float(t08.get("delta_tracking", {}).get("science_facing_target_rows", 0))
    t09_seam_rows = float(t09.get("execution_packet", {}).get("queue_row_count", 0))

    delta = t12.get("go_no_go_contract", {}).get("delta_fields", {})
    science_surface_share_delta = float(delta.get("science_surface_share_delta", 0.0))
    theorem_depth_queue_delta = float(delta.get("theorem_depth_queue_delta", 0))
    seam_empirical_packet_delta = float(delta.get("seam_empirical_packet_delta", 0))
    controls_overhead_delta = float(delta.get("controls_overhead_delta", 0.0))
    t13_metrics = t13.get("live_matrix_packet", {}).get("execution_evidence", {}).get("packet_metrics", {})
    t14 = _read_json(T14_PATH) if T14_PATH.exists() else {}
    t14_metrics = t14.get("live_matrix_packet", {}).get("execution_evidence", {}).get("packet_metrics", {})
    t13_science_signal = float(
        t13_metrics.get("theorem_depth_queue_delta", 0.0) + t13_metrics.get("seam_empirical_packet_delta", 0.0)
    )
    t13_controls_signal = float(t13_metrics.get("rolling_controls_signal", controls_overhead_delta))
    t14_science_signal = float(
        t14_metrics.get("theorem_depth_queue_delta", 0.0) + t14_metrics.get("seam_empirical_packet_delta", 0.0)
    )
    t14_controls_signal = float(t14_metrics.get("rolling_controls_signal", t13_controls_signal))

    packet_index = int(
        t14.get("live_matrix_packet", {}).get("promotion_decision", {}).get(
            "current_packet_id",
            t13.get("live_matrix_packet", {}).get("promotion_decision", {}).get("current_packet_id", 1),
        )
    )

    science_signal_series = [
        0.0,
        t08_science_rows,
        t09_seam_rows,
        theorem_depth_queue_delta + seam_empirical_packet_delta,
        t13_science_signal,
        t14_science_signal,
    ]
    controls_signal_series = [0.0, 0.0, 0.0, controls_overhead_delta, t13_controls_signal, t14_controls_signal]

    return {
        "window_size": 6,
        "packet_index": packet_index,
        "science_signal_series": science_signal_series,
        "controls_signal_series": controls_signal_series,
        "science_signal_rolling_mean": round(rolling_mean(science_signal_series), 6),
        "controls_signal_rolling_mean": round(rolling_mean(controls_signal_series), 6),
        "science_surface_share_delta": science_surface_share_delta,
    }


def main() -> int:
    m = compute_metrics()
    print(
        "rolling_window_metrics: "
        f"science_signal_rolling_mean={m['science_signal_rolling_mean']} "
        f"controls_signal_rolling_mean={m['controls_signal_rolling_mean']} "
        f"science_surface_share_delta={m['science_surface_share_delta']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
