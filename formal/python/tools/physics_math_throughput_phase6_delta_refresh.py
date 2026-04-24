from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
BASELINE_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_baseline_20260407_v0.json"
T08_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase3_t08_theorem_depth_execution_packet_20260407_v0.json"
T09_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase4_t09_seam_empirical_execution_packet_20260407_v0.json"
T12_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json"


def _read_json(path: Path) -> dict:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def compute_proxy_deltas() -> dict:
    baseline = _read_json(BASELINE_PATH)
    t08 = _read_json(T08_PATH)
    t09 = _read_json(T09_PATH)

    total_test_files = baseline["counts"]["total_test_files"]
    metadata_to_science_line_ratio = baseline["ratios"]["metadata_to_science_line_ratio"]

    theorem_depth_rows = int(t08.get("delta_tracking", {}).get("science_facing_target_rows", 0))
    seam_rows = int(t09.get("execution_packet", {}).get("queue_row_count", 0))

    science_surface_share_delta = round((theorem_depth_rows + seam_rows) / total_test_files, 6)
    controls_overhead_delta = round(1.0 / metadata_to_science_line_ratio, 6)

    return {
        "science_surface_share_delta": science_surface_share_delta,
        "theorem_depth_queue_delta": theorem_depth_rows,
        "seam_empirical_packet_delta": seam_rows,
        "controls_overhead_delta": controls_overhead_delta,
    }


def refresh_t12_checkpoint() -> dict:
    t12 = _read_json(T12_PATH)
    deltas = compute_proxy_deltas()

    contract = t12.setdefault("go_no_go_contract", {})
    contract["delta_fields"] = {
        **contract.get("delta_fields", {}),
        **deltas,
    }
    contract["delta_provenance"] = {
        "refresh_tool": "formal/python/tools/physics_math_throughput_phase6_delta_refresh.py",
        "method": "proxy_from_baseline_and_execution_packets",
        "phase3_t08_source": "formal/output/reports/physics_math_throughput_phase3_t08_theorem_depth_execution_packet_20260407_v0.json",
        "phase4_t09_source": "formal/output/reports/physics_math_throughput_phase4_t09_seam_empirical_execution_packet_20260407_v0.json",
    }

    required = set(contract.get("required_green_gates", []))
    required.add("formal/python/tests/test_physics_math_throughput_phase6_non_placeholder_delta_gate.py")
    contract["required_green_gates"] = sorted(required)

    T12_PATH.write_text(json.dumps(t12, indent=2) + "\n", encoding="utf-8")
    return deltas


def main() -> int:
    deltas = refresh_t12_checkpoint()
    print(
        "phase6_delta_refresh: "
        f"science_surface_share_delta={deltas['science_surface_share_delta']} "
        f"theorem_depth_queue_delta={deltas['theorem_depth_queue_delta']} "
        f"seam_empirical_packet_delta={deltas['seam_empirical_packet_delta']} "
        f"controls_overhead_delta={deltas['controls_overhead_delta']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
