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
    / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_08_PHASE3_THEOREM_DEPTH_EXECUTION_PACKET_20260407_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase3_t08_theorem_depth_execution_packet_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase3_t08_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing phase3 tranche08 declaration."
    assert CHECKPOINT_PATH.exists(), "Missing phase3 tranche08 checkpoint artifact."


def test_phase3_t08_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE3_T08_THEOREM_DEPTH_EXECUTION_PACKET",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_T08_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_08_PHASE3_THEOREM_DEPTH_EXECUTION_PACKET_20260407_v0.md",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_T08_CHECKPOINT_v0: formal/output/reports/physics_math_throughput_phase3_t08_theorem_depth_execution_packet_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_T08_GATE_v0: formal/python/tests/test_physics_math_throughput_phase3_t08_theorem_depth_execution_packet_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_EXECUTION_MODE_v0: BOUNDED_THEOREM_DEPTH_PACKET_WITH_DEBT_BINDING",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_EXECUTION_STATUS_v0: EXECUTION_PACKET_DECLARED_NONLIVE_NONCLAIM",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE3_STOP_CONDITION_v0: HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_DEPTH_PACKET_SCOPE_DRIFT",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing phase3 tranche08 program token(s): " + ", ".join(missing)


def test_phase3_t08_checkpoint_contract() -> None:
    payload = _read_json(CHECKPOINT_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_PHASE3_T08_THEOREM_DEPTH_EXECUTION_PACKET_v0"
    assert payload.get("status") == "PHASE3_T08_EXECUTION_PACKET_DECLARED_NONLIVE_NONCLAIM"

    packet = payload.get("execution_packet", {})
    assert packet.get("packet_mode") == "BOUNDED_THEOREM_DEPTH_PACKET_WITH_DEBT_BINDING"
    assert packet.get("queue_row_count") == 3
    rows = packet.get("rows", [])
    assert len(rows) == 3
    for row in rows:
        assert row.get("queue_id")
        assert row.get("target_surface")
        assert row.get("target_class") in {"THEOREM_SURFACE", "DISCHARGE_SUPPORT_SURFACE"}
        assert row.get("debt_binding_pointer")
        assert row.get("execution_state") == "QUEUED_NONLIVE"

    delta = payload.get("delta_tracking", {})
    assert delta.get("science_facing_target_rows") == 3
    assert delta.get("metadata_only_target_rows") == 0
    assert delta.get("depth_packet_scope_drift") is False

    controls = payload.get("controls", {})
    assert controls.get("release_gate_truth_changed") is False
    assert controls.get("nonclaim_boundary_changed") is False
    assert controls.get("packet_policy_changed") is False
    assert controls.get("scalar_freeze_policy_changed") is False
    assert controls.get("execution_live_enabled") is False
    assert controls.get("stop_condition") == "HALT_ON_RELEASE_GATE_OR_NONCLAIM_OR_DEPTH_PACKET_SCOPE_DRIFT"
