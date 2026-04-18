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
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_01_RETRO_TRUTH_ALIGNMENT_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase1_retro_truth_alignment_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase1_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing phase1 tranche declaration."
    assert CHECKPOINT_PATH.exists(), "Missing phase1 checkpoint artifact."


def test_phase1_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE1_RETRO_TRUTH_ALIGNMENT_PREP",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_01_RETRO_TRUTH_ALIGNMENT_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase1_retro_truth_alignment_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_GATE_v0: formal/python/tests/test_physics_math_throughput_phase1_retro_truth_alignment_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_RETRO_DECISION_SCOPE_v0: SELECTIVE_DOWNGRADE_CANDIDATE_SET_DECLARED_NONCLAIM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_STATUS_MUTATION_v0: NOT_EXECUTED_IN_T01",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_STOP_CONDITION_v0: HALT_ON_RELEASE_GATE_OR_NONCLAIM_DRIFT",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing phase1 program token(s): " + ", ".join(missing)


def test_phase1_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE1_RETRO_ALIGNMENT_v0"
    assert payload.get("status") == "PHASE1_PREP_DECLARED_NONCLAIM"

    scope = payload.get("retroactive_alignment_scope", {})
    assert scope.get("selective_downgrades_enabled") is True
    assert scope.get("status_mutation_executed") is False
    assert scope.get("candidate_set_size") == 3

    candidates = scope.get("candidate_set", [])
    assert len(candidates) == 3
    for row in candidates:
        assert row.get("candidate_id"), "Each candidate must define candidate_id"
        assert row.get("surface"), "Each candidate must define surface"
        assert row.get("proposed_action") == "DOWNGRADE_CANDIDATE_DECLARE_ONLY"
        assert row.get("debt_binding_pointer"), "Each candidate must bind a debt/evidence pointer"

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("packet_policy_changed") is False
    assert controls.get("scalar_freeze_policy_changed") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_DRIFT"
