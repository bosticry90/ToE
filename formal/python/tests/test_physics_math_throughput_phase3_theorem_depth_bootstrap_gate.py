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
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_05_PHASE3_THEOREM_DEPTH_BOOTSTRAP_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase3_theorem_depth_bootstrap_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase3_t05_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing phase3 tranche05 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing phase3 tranche05 checkpoint artifact."


def test_phase3_t05_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE3_T05_THEOREM_DEPTH_ACCELERATION_BOOTSTRAP",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_T05_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_05_PHASE3_THEOREM_DEPTH_BOOTSTRAP_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_T05_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase3_theorem_depth_bootstrap_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_T05_GATE_v0: formal/python/tests/test_physics_math_throughput_phase3_theorem_depth_bootstrap_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_DEPTH_OBJECTIVE_v0: INCREASE_SCIENCE_FACING_THEOREM_AND_DISCHARGE_SURFACE_SHARE",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_EXECUTION_STATUS_v0: BOOTSTRAP_DECLARED_NONLIVE_NONCLAIM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_STOP_CONDITION_v0: HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_DEPTH_POLICY_DRIFT",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing phase3 tranche05 program token(s): " + ", ".join(missing)


def test_phase3_t05_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE3_THEOREM_DEPTH_BOOTSTRAP_v0"
    assert payload.get("status") == "PHASE3_BOOTSTRAP_DECLARED_NONLIVE_NONCLAIM"

    policy = payload.get("depth_acceleration_policy", {})
    assert policy.get("queue_model") == "SCIENCE_FACING_THEOREM_DEPTH_FIRST"
    assert isinstance(policy.get("priority_buckets"), list) and len(policy.get("priority_buckets")) >= 3

    bindings = policy.get("mandatory_bindings", {})
    assert bindings.get("proof_debt_traceability_pointer") == "formal/docs/release/TOE_PROOF_DEBT_WITNESS_TRACEABILITY_v0.md"
    assert bindings.get("burndown_checkpoint_pointer") == "formal/output/proof_debt_burndown_checkpoint_cycle05_v0.json"
    assert policy.get("execution_live_enabled") is False

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("packet_policy_changed") is False
    assert controls.get("scalar_freeze_policy_changed") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_DEPTH_POLICY_DRIFT"
