from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_06_PHASE4_SEAM_EMPIRICAL_BOOTSTRAP_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase4_seam_empirical_bootstrap_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase4_t06_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing phase4 tranche06 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing phase4 tranche06 checkpoint artifact."


def test_phase4_t06_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE4_T06_SEAM_EMPIRICAL_THROUGHPUT_BOOTSTRAP",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_T06_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_06_PHASE4_SEAM_EMPIRICAL_BOOTSTRAP_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_T06_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase4_seam_empirical_bootstrap_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_T06_GATE_v0: formal/python/tests/test_physics_math_throughput_phase4_seam_empirical_bootstrap_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_OBJECTIVE_v0: INCREASE_SEAM_AND_EMPIRICAL_PACKET_THROUGHPUT_WITH_DEBT_BINDINGS",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_EXECUTION_STATUS_v0: BOOTSTRAP_DECLARED_NONLIVE_NONCLAIM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE4_STOP_CONDITION_v0: HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_SEAM_PACKET_DRIFT",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing phase4 tranche06 program token(s): " + ", ".join(missing)


def test_phase4_t06_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE4_SEAM_EMPIRICAL_BOOTSTRAP_v0"
    assert payload.get("status") == "PHASE4_BOOTSTRAP_DECLARED_NONLIVE_NONCLAIM"

    policy = payload.get("seam_empirical_policy", {})
    assert policy.get("queue_model") == "SEAM_PROMOTION_AND_PACKET_COUPLING_FIRST"
    assert isinstance(policy.get("priority_buckets"), list) and len(policy.get("priority_buckets")) >= 3

    bindings = policy.get("mandatory_bindings", {})
    assert bindings.get("proof_debt_traceability_pointer") == "formal/docs/release/TOE_PROOF_DEBT_WITNESS_TRACEABILITY_v0.md"
    assert bindings.get("packet05_ledger_pointer") == "formal/output/empirical_packet05_decision_ledger_v0.json"
    assert policy.get("execution_live_enabled") is False

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("packet_policy_changed") is False
    assert controls.get("scalar_freeze_policy_changed") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_SEAM_PACKET_DRIFT"
