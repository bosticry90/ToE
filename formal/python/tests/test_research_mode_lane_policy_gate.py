from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import (
    RESEARCH_MODE_BOUNDARY_v0,
    RESEARCH_MODE_LOOP_DISCIPLINE_v0,
    RESEARCH_MODE_NAMESPACE_v0,
    RESEARCH_MODE_v0,
)


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md"
SCHEMA_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md"
RETENTION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md"
RUNNER_PATH = REPO_ROOT / "research_mode_execution.ps1"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


REQUIRED_POLICY_TOKENS = (
    "RESEARCH_MODE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
    "RESEARCH_MODE_MODEL_v0: RESEARCH_FIRST_WITH_SANDBOX_AND_PROMOTION_BOUNDARY",
    "RESEARCH_MODE_ALLOWED_OUTPUTS_v0: LOCAL_DERIVATION_REDUCTION_SIMULATION_COUNTEREXAMPLE_RETAIN_PRUNE_INCONCLUSIVE_AND_DESIGN_ONLY",
    "RESEARCH_MODE_FORBIDDEN_OUTPUTS_v0: NO_CANONICAL_ROW_MUTATION_NO_RELEASE_GATE_TRUTH_CHANGE_NO_SEAM_CLASS_FLIP_NO_MASTER_ACTION_RECLASSIFICATION_NO_EXTERNAL_TRUTH_CLAIM",
    "RESEARCH_MODE_LOOP_DISCIPLINE_v0: ONE_OBJECT_ONE_QUESTION_ONE_TEST_ONE_OUTPUT",
    "RESEARCH_MODE_MINIMUM_METADATA_SCHEMA_v0: formal/docs/release/RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md",
    "RESEARCH_MODE_RETENTION_POLICY_v0: formal/docs/release/RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0.md",
    "RESEARCH_MODE_AUTHORITY_MATRIX_v0: formal/docs/release/RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
    "RESEARCH_MODE_NAMESPACE_v0: formal/python/research",
    "RESEARCH_MODE_RUNNER_v0: research_mode_execution.ps1",
    "RESEARCH_MODE_GATE_v0: formal/python/tests/test_research_mode_lane_policy_gate.py",
    "RESEARCH_MODE_PROMOTION_BINDING_v0: RESEARCH_OUTPUTS_MUST_PASS_THROUGH_SANDBOX_AND_PROMOTION_GOVERNANCE_BEFORE_CANONICAL_MUTATION",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_research_mode_policy_surfaces_have_required_tokens() -> None:
    policy_text = _read(POLICY_PATH)
    retention_text = _read(RETENTION_PATH)
    matrix_text = _read(MATRIX_PATH)

    for token in REQUIRED_POLICY_TOKENS:
        assert token in policy_text

    assert "RESEARCH_ARTIFACT_RETENTION_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM" in retention_text
    assert "RESEARCH_MODE_AUTHORITY_LADDER_v0: RESEARCH_MODE_TO_SANDBOX_TO_PROMOTION_GOVERNANCE_TO_CANONICAL" in matrix_text


def test_research_mode_namespace_markers_are_pinned() -> None:
    assert RESEARCH_MODE_v0 is True
    assert RESEARCH_MODE_NAMESPACE_v0 == "formal.python.research"
    assert RESEARCH_MODE_BOUNDARY_v0 == "RESEARCH_ONLY_NO_CANONICAL_MUTATION"
    assert RESEARCH_MODE_LOOP_DISCIPLINE_v0 == "ONE_OBJECT_ONE_QUESTION_ONE_TEST_ONE_OUTPUT"


def test_research_mode_mirrors_and_runner_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md",
        "formal/docs/release/RESEARCH_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md",
        "formal/docs/release/RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0.md",
        "formal/docs/release/RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
        "formal/python/tests/test_research_mode_lane_policy_gate.py",
        "formal/python/tests/test_research_mode_metadata_schema_gate.py",
        "research_mode_execution.ps1",
        "formal/python/research",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "Research Mode (2026-04-19)" in readme_text
    assert "research_mode_execution.ps1" in readme_text
    assert RUNNER_PATH.exists()
    assert SCHEMA_PATH.exists()


def test_research_mode_boundary_remains_fail_closed() -> None:
    policy_text = _read(POLICY_PATH)
    matrix_text = _read(MATRIX_PATH)

    assert "This policy does not authorize canonical promotion" in policy_text
    assert "No matrix row may assign canonical mutation authority to research mode." in matrix_text