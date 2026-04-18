from __future__ import annotations

from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_INTEGRATION_v0.md"
)
ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "information_constraint_operational_position_integration_v0.json"
)
FOCUSED_GATE_PATH = (
    REPO_ROOT / "formal" / "python" / "tests" / "test_information_constraint_operational_position_integration_gate.py"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_information_constraint_authority_artifacts_exist() -> None:
    assert TARGET_PATH.exists(), "Missing information-constraint target doc."
    assert ARTIFACT_PATH.exists(), "Missing information-constraint artifact."
    assert FOCUSED_GATE_PATH.exists(), "Missing focused information-constraint gate."


def test_information_constraint_authority_tokens_are_parity_pinned() -> None:
    state_active = _active_text(STATE_PATH)
    roadmap_active = _active_text(ROADMAP_PATH)

    parity_tokens = [
        "THEORY_RESTART_T19_INFORMATION_CONSTRAINT_STATUS_v0: FOUNDATION_PINNED_NONCLAIM",
        "THEORY_RESTART_T19_INFORMATION_CONSTRAINT_TARGET_v0: formal/docs/paper/DERIVATION_TARGET_INFORMATION_CONSTRAINT_OPERATIONAL_POSITION_INTEGRATION_v0.md",
        "THEORY_RESTART_T19_INFORMATION_CONSTRAINT_ARTIFACT_v0: formal/output/information_constraint_operational_position_integration_v0.json",
        "THEORY_RESTART_T19_INFORMATION_CONSTRAINT_GATE_v0: formal/python/tests/test_information_constraint_operational_position_integration_gate.py",
        "THEORY_RESTART_T19_INFORMATION_CONSTRAINT_AUTHORITY_PARITY_GATE_v0: formal/python/tests/test_information_constraint_operational_position_authority_parity_gate.py",
        "THEORY_RESTART_T19_INFORMATION_CONSTRAINT_PACKET42_HOLD_INVARIANCE_v0: ENFORCED",
    ]

    for token in parity_tokens:
        assert token in state_active, f"Missing state token: {token}"
        assert token in roadmap_active, f"Missing roadmap token: {token}"
