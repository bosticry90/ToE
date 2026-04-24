from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_11_PROGRAM_CLOSEOUT_READINESS_20260407_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase5_t11_program_closeout_readiness_20260407_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase5_t11_files_exist() -> None:
    assert PROGRAM_PATH.exists()
    assert DECLARATION_PATH.exists()
    assert CHECKPOINT_PATH.exists()


def test_phase5_t11_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE5_T11_PROGRAM_CLOSEOUT_READINESS",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_T11_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_11_PROGRAM_CLOSEOUT_READINESS_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_T11_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase5_t11_program_closeout_readiness_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE5_T11_GATE_v0: formal/python/tests/test_physics_math_throughput_phase5_t11_program_closeout_readiness_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_SUMMARY_GATE_v0: formal/python/tests/test_physics_math_throughput_program_closeout_summary_gate.py",
    ]
    missing = [token for token in required if token not in text]
    assert not missing


def test_phase5_t11_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE5_T11_PROGRAM_CLOSEOUT_READINESS_v0"
    assert payload.get("status") == "PHASE5_T11_CLOSEOUT_READINESS_DECLARED_NONLIVE_NONCLAIM"

    contract = payload.get("coverage_contract", {})
    assert contract.get("declared_tranche_count") == 12
    assert len(contract.get("tranche_ids", [])) == 12
    assert contract.get("summary_gate") == "formal/python/tests/test_physics_math_throughput_program_closeout_summary_gate.py"

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("execution_live_enabled") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_CLOSEOUT_DRIFT"
