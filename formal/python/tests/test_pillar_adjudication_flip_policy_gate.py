from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
PACK_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "QFT_DISCHARGE_READINESS_PACK_v0.md"

REQUIRED_FLIP_POLICY_GATES = [
    "formal/python/tests/test_qft_discharge_readiness_pack_gate.py",
    "formal/python/tests/test_qft_full_derivation_discharge_gate.py",
    "formal/python/tests/test_pillar_adjudication_cross_surface_consistency_gate.py",
    "formal/python/tests/test_qft_full_derivation_legacy_retirement_gate.py",
    "formal/python/tests/test_token_migration_window_gate.py",
    "formal/python/tests/test_state_claim_traceability_audit_gate.py",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_flip_policy_is_explicitly_locked_to_readiness_and_governance_gates() -> None:
    pack_text = _read(PACK_PATH)

    assert "## ADJUDICATION_FLIP_POLICY" in pack_text
    assert "FLIP_REQUIRES_READINESS_PACK_AND_POLICY_GATE_CLOSURE" in pack_text

    for gate_rel in REQUIRED_FLIP_POLICY_GATES:
        gate_path = REPO_ROOT / gate_rel
        assert gate_path.exists(), f"Missing required flip-policy gate file `{gate_rel}`."
        assert gate_rel in pack_text, f"Flip-policy gate `{gate_rel}` must be pinned in readiness pack."
