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
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_toe_master_action_assumption_classification_surface_is_explicit() -> None:
    text = _read(REGISTRY_PATH)

    required = (
        "TOE_MASTER_ACTION_ASSUMPTION_CLASSIFICATION_STATUS_v0: SCAFFOLD_PINNED_NONCLAIM",
        "Class A (theorem-linked constraints)",
        "Class B (policy-level placeholders)",
        "Class C (speculative scaffolds)",
        "Reduce duplicated policy assumptions across lane docs.",
        "Promote Class B entries to Class A only with explicit theorem witness pointers.",
        "Keep Class C entries explicit and non-promoted until bridge and transport closure exists.",
    )
    for token in required:
        assert token in text, f"Assumption classification registry missing `{token}`."
