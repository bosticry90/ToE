from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RULE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYSICS_FIRST_EXECUTION_RULE_v0.md"
STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "UNIFIED_TRANCHE_STANDARD_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_physics_first_rule_doc_exists() -> None:
    assert RULE_PATH.exists(), "Missing PHYSICS_FIRST_EXECUTION_RULE_v0.md"
    assert STANDARD_PATH.exists(), "Missing UNIFIED_TRANCHE_STANDARD_v0.md"


def test_physics_first_rule_contains_required_classes_and_constraints() -> None:
    text = _read(RULE_PATH)
    required_tokens = [
        "PHYSICS_FIRST_EXECUTION_RULE_v0",
        "math_strengthening",
        "physics_compatibility",
        "blocker_discharge",
        "assumption_narrowing",
        "prediction_or_exclusion",
        "support-only tranche is marked active",
        "one active scientific lane at a time",
        "at most one queued lane",
        "governance prerequisite plus full pytest",
        "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        "Support-only governance work cannot become active science",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Physics-first rule doc missing required token(s): " + ", ".join(missing)


def test_unified_tranche_standard_includes_four_modes_and_required_fields() -> None:
    text = _read(STANDARD_PATH)
    required_tokens = [
        "UNIFIED_TRANCHE_STANDARD_v0",
        "kickoff",
        "increment",
        "synthesis",
        "decision",
        "scientific_delta_class",
        "evidence_artifact",
        "gate_test",
        "status_transition",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Unified tranche standard missing required token(s): " + ", ".join(missing)
