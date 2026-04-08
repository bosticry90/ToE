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
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_02_FIRST_SELECTIVE_DOWNGRADE_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase1_t02_selective_downgrade_execution_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase1_t02_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing phase1 tranche02 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing phase1 tranche02 checkpoint artifact."


def test_phase1_t02_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE1_T02_SELECTIVE_DOWNGRADE_EXECUTION",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_T02_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_02_FIRST_SELECTIVE_DOWNGRADE_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_T02_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase1_t02_selective_downgrade_execution_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_T02_GATE_v0: formal/python/tests/test_physics_math_throughput_phase1_t02_selective_downgrade_execution_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_RETRO_DECISION_SCOPE_v0: SELECTIVE_DOWNGRADE_EXECUTION_BOUNDED_SINGLE_CANDIDATE",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_STATUS_MUTATION_v0: EXECUTED_IN_T02_BOUNDED_NONCLAIM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_T02_REUPGRADE_CRITERIA_v0: EVIDENCE_BINDING_PLUS_GATE_STABILITY_PLUS_RELEASE_TRUTH_INVARIANCE",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE1_STOP_CONDITION_v0: HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_RETRO_SCOPE_DRIFT",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing phase1 tranche02 program token(s): " + ", ".join(missing)


def test_phase1_t02_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE1_T02_SELECTIVE_DOWNGRADE_EXECUTION_v0"
    assert payload.get("status") == "PHASE1_T02_EXECUTED_BOUNDED_NONCLAIM"

    scope = payload.get("execution_scope", {})
    assert scope.get("selective_downgrades_enabled") is True
    assert scope.get("status_mutation_executed") is True
    assert scope.get("candidate_set_size") == 3
    assert scope.get("executed_candidate_set_size") == 1
    assert scope.get("executed_candidate_ids") == ["RETRO_CANDIDATE_03"]

    rows = scope.get("executed_rows", [])
    assert len(rows) == 1
    row = rows[0]
    assert row.get("candidate_id") == "RETRO_CANDIDATE_03"
    assert row.get("surface") == "formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
    assert row.get("mutation_type") == "RETROACTIVE_STATUS_RECLASSIFICATION"
    assert row.get("debt_binding_pointer")
    assert isinstance(row.get("reupgrade_criteria"), list) and len(row.get("reupgrade_criteria")) >= 3

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("packet_policy_changed") is False
    assert controls.get("scalar_freeze_policy_changed") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_RETRO_SCOPE_DRIFT"
