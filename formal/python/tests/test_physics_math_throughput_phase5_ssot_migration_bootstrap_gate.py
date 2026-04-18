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
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_07_PHASE5_SSOT_MIGRATION_BOOTSTRAP_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase5_ssot_migration_bootstrap_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase5_t07_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing phase5 tranche07 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing phase5 tranche07 checkpoint artifact."


def test_phase5_t07_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE5_T07_SSOT_AUTHORITY_MIGRATION_BOOTSTRAP",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_T07_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_07_PHASE5_SSOT_MIGRATION_BOOTSTRAP_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_T07_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase5_ssot_migration_bootstrap_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_T07_GATE_v0: formal/python/tests/test_physics_math_throughput_phase5_ssot_migration_bootstrap_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_OBJECTIVE_v0: SSOT_AUTHORITY_SURFACE_ALIGNMENT_AND_INSTITUTIONALIZATION_BOOTSTRAP",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_EXECUTION_STATUS_v0: BOOTSTRAP_DECLARED_NONLIVE_NONCLAIM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_STOP_CONDITION_v0: HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_SSOT_BOUNDARY_DRIFT",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing phase5 tranche07 program token(s): " + ", ".join(missing)


def test_phase5_t07_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE5_SSOT_MIGRATION_BOOTSTRAP_v0"
    assert payload.get("status") == "PHASE5_BOOTSTRAP_DECLARED_NONLIVE_NONCLAIM"

    policy = payload.get("ssot_migration_policy", {})
    assert isinstance(policy.get("authority_hierarchy"), list) and len(policy.get("authority_hierarchy")) >= 3
    assert isinstance(policy.get("migration_sequence"), list) and len(policy.get("migration_sequence")) >= 4
    assert policy.get("execution_live_enabled") is False

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("packet_policy_changed") is False
    assert controls.get("scalar_freeze_policy_changed") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_SSOT_BOUNDARY_DRIFT"
