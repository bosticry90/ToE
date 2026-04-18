from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_03_PHASE2_LANE_SPLIT_BOOTSTRAP_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase2_lane_split_bootstrap_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase2_t03_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing phase2 tranche03 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing phase2 tranche03 checkpoint artifact."


def test_phase2_t03_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE2_LANE_SPLIT_BOOTSTRAP",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_T03_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_03_PHASE2_LANE_SPLIT_BOOTSTRAP_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_T03_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase2_lane_split_bootstrap_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_T03_GATE_v0: formal/python/tests/test_physics_math_throughput_phase2_lane_split_bootstrap_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_LANE_MODEL_v0: DUAL_TRACK_GOVERNANCE_AND_SCIENCE_WITH_RELEASE_TRUTH_LOCK",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_EXECUTION_STATUS_v0: BOOTSTRAP_DECLARED_NONLIVE_NONCLAIM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE2_STOP_CONDITION_v0: HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_LANE_BOUNDARY_DRIFT",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing phase2 tranche03 program token(s): " + ", ".join(missing)


def test_phase2_t03_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE2_LANE_SPLIT_BOOTSTRAP_v0"
    assert payload.get("status") == "PHASE2_BOOTSTRAP_DECLARED_NONLIVE_NONCLAIM"

    topology = payload.get("lane_topology", {})
    gov_lane = topology.get("governance_integrity_lane", {})
    sci_lane = topology.get("science_throughput_lane", {})
    merge_policy = topology.get("merge_policy", {})

    assert gov_lane.get("lane_id") == "LANE_GOV_INTEGRITY"
    assert sci_lane.get("lane_id") == "LANE_SCIENCE_THROUGHPUT"
    assert merge_policy.get("cross_lane_merge_enabled") is False
    required_conditions = {
        "release_gate_truth_invariance",
        "nonclaim_boundary_invariance",
        "lane_boundary_integrity",
    }
    observed_conditions = set(merge_policy.get("cross_lane_merge_requires", []))
    assert required_conditions.issubset(observed_conditions)

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("packet_policy_changed") is False
    assert controls.get("scalar_freeze_policy_changed") is False
    assert controls.get("execution_live_enabled") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_LANE_BOUNDARY_DRIFT"
