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
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_phase6_t12_live_authorization_decision_packet_20260407_v0.json"
DECISION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T14_POST_T13_DUAL_CANDIDATE_LANE_AUTHORIZATION_DECISION_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase6_policy_approval_files_exist() -> None:
    assert PROGRAM_PATH.exists()
    assert CHECKPOINT_PATH.exists()
    assert DECISION_PATH.exists()


def test_phase6_program_token_for_policy_approval_gate() -> None:
    text = _read(PROGRAM_PATH)
    token = (
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_POLICY_APPROVAL_GATE_v0: "
        "formal/python/tests/test_physics_math_throughput_phase6_policy_approval_binding_gate.py"
    )
    assert token in text


def test_phase6_checkpoint_requires_policy_approval_gate() -> None:
    payload = _read_json(CHECKPOINT_PATH)
    go_no_go = payload.get("go_no_go_contract", {})
    required_green = set(go_no_go.get("required_green_gates", []))
    assert "formal/python/tests/test_physics_math_throughput_phase6_policy_approval_binding_gate.py" in required_green

    approval_binding = payload.get("approval_binding", {})
    assert approval_binding.get("decision_artifact") == "formal/docs/release/WS_10_T14_POST_T13_DUAL_CANDIDATE_LANE_AUTHORIZATION_DECISION_v0.md"
    assert approval_binding.get("approval_status") == "APPROVAL_BOUND_NONLIVE"


def test_t14_decision_contains_machine_checkable_approval_fields() -> None:
    text = _read(DECISION_PATH)
    required_lines = [
        "approval_authority:",
        "approval_timestamp_utc:",
        "approval_scope_token:",
        "approval_expiry_utc:",
        "authorized_live_envelope:",
    ]
    missing = [line for line in required_lines if line not in text]
    assert not missing
