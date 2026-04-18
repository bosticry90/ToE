from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_LANGUAGE_ENFORCEMENT_POLICY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
README_PATH = REPO_ROOT / "README.md"
CLOSURE_STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_CLOSURE_SEMANTICS_STANDARD_v0.md"


REQUIRED_POLICY_TOKENS = (
    "LANGUAGE_RULE_01_v0: STATUS_SUMMARIES_REQUIRE_LAYER_QUALIFIED_CLOSURE",
    "LANGUAGE_RULE_02_v0: UNQUALIFIED_COMPLETE_CLOSED_DISCHARGED_PROHIBITED_IN_INTERPRETATION_LINES",
    "LANGUAGE_RULE_03_v0: SEAM_GOVERNANCE_COMPLETE_DOES_NOT_IMPLY_SEAM_PHYSICS_COMPLETE",
    "LANGUAGE_RULE_04_v0: TERMINAL_REPO_COMPLETION_TOKENS_ARE_NONCLAIM_SCOPE",
    "ALLOWED_v0_PHYSICS_CLOSED_UNDER_BOUNDED_DERIVATION_SCOPE",
    "ALLOWED_v0_GOVERNANCE_CLOSED_PER_CANONICAL_POLICY_SCOPE",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_language_enforcement_policy_has_required_controls() -> None:
    text = _read(POLICY_PATH)
    for token in REQUIRED_POLICY_TOKENS:
        assert token in text


def test_policy_is_cross_pinned_in_canonical_surfaces() -> None:
    policy_rel = "formal/docs/release/TOE_LANGUAGE_ENFORCEMENT_POLICY_v0.md"

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    readme_text = _read(README_PATH)
    closure_text = _read(CLOSURE_STANDARD_PATH)

    assert policy_rel in roadmap_text
    assert policy_rel in state_text
    assert policy_rel in closure_text
    assert "TERMINAL_SATISFIED_v0_NONCLAIM" in readme_text
    assert "This is NOT a physics-complete ToE claim." in readme_text
