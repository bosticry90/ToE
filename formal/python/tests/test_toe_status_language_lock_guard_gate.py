from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_LANGUAGE_ENFORCEMENT_POLICY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_readme_project_status_uses_locked_nonclaim_language() -> None:
    text = _read(README_PATH)

    assert "Governance status is TERMINAL_SATISFIED_v0_NONCLAIM under pinned policy scope." in text
    assert "Physics status is MIXED_PROGRESS_v0 with seam-level physics closure still incomplete." in text
    assert "This is NOT a physics-complete ToE claim." in text

    # Lock out the legacy ambiguous one-liner so it cannot drift back in.
    assert "Governance status is terminal-satisfied under bounded non-claim semantics; seam-level physics closure remains incomplete." not in text


def test_state_has_seam_interpretation_rule_tokens() -> None:
    text = _read(STATE_PATH)
    assert "SEAM_STATUS_INTERPRETATION_RULE_v0: GOVERNANCE_COMPLETE_DOES_NOT_IMPLY_PHYSICS_COMPLETE" in text
    assert "SEAM_PHYSICS_COMPLETION_SCOPE_RULE_v0: PHYSICS_COMPLETE_REQUIRES_EXPLICIT_BLOCKER_DISCHARGE_BASIS" in text
    assert "formal/docs/release/TOE_LANGUAGE_ENFORCEMENT_POLICY_v0.md" in text


def test_roadmap_has_layer_qualifier_reference_tokens() -> None:
    text = _read(ROADMAP_PATH)
    assert "PROCEED_GATE_LAYER_QUALIFIER_v0: ALLOWED_v0_PHYSICS_CLOSED_UNDER_BOUNDED_DERIVATION_SCOPE" in text
    assert "MATRIX_CLOSURE_GATE_LAYER_QUALIFIER_v0: ALLOWED_v0_GOVERNANCE_CLOSED_PER_CANONICAL_POLICY_SCOPE" in text
    assert "CLOSURE_SCOPE_BOUNDARY_REFERENCE_v0: formal/docs/release/TOE_LANGUAGE_ENFORCEMENT_POLICY_v0.md" in text


def test_policy_cross_pins_this_guard_gate() -> None:
    text = _read(POLICY_PATH)
    assert "formal/python/tests/test_toe_status_language_lock_guard_gate.py" in text
