from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
POLICY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REPOSITORY_ARTIFACT_RETENTION_POLICY_20260505_v0.md"
)
RESEARCH_POLICY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_repository_artifact_retention_policy_records_required_tokens() -> None:
    text = _read(POLICY_PATH)
    research_text = _read(RESEARCH_POLICY_PATH)

    for token in {
        "REPOSITORY_ARTIFACT_RETENTION_POLICY_20260505_v0",
        "REPOSITORY_ARTIFACT_RETENTION_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "REPOSITORY_ARTIFACT_RETENTION_TRACKED_CANONICAL_v0: SCHEMAS_RELEASE_PACKETS_LEAN_SURFACES_SMALL_SUMMARIES",
        "REPOSITORY_ARTIFACT_RETENTION_GENERATED_OUTPUT_RULE_v0: VERIFY_BY_DEFAULT_WRITE_ONLY_WITH_EXPLICIT_REGEN_AUTHORIZATION",
        "REPOSITORY_ARTIFACT_RETENTION_TRACKED_WRITE_ENV_v0: TOE_ALLOW_TRACKED_OUTPUT_WRITES=1",
        "REPOSITORY_ARTIFACT_RETENTION_LARGE_SNAPSHOT_FREEZE_v0: NO_NEW_LARGE_TRACKED_SNAPSHOTS_BY_DEFAULT",
        "REPOSITORY_ARTIFACT_RETENTION_EXISTING_SNAPSHOT_DISPOSITION_v0: RETAIN_UNTIL_EXPLICIT_MIGRATION_PACKET",
        "REPOSITORY_ARTIFACT_RETENTION_MIGRATION_AUTHORITY_v0: FUTURE_EXPLICIT_PACKET_REQUIRED",
        "REPOSITORY_ARTIFACT_RETENTION_NONCLAIM_BOUNDARY_v0: NO_SCIENTIFIC_AUTHORITY_CHANGE",
        "RESEARCH_ARTIFACT_RETENTION_POLICY_20260419_v0",
    }:
        assert token in text

    assert "RESEARCH_ARTIFACT_RETENTION_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM" in research_text


def test_repository_artifact_retention_policy_classifies_risky_roots() -> None:
    text = _read(POLICY_PATH)

    for root in {
        "formal/docs/release",
        "formal/toe_formal",
        "formal/python/tests",
        "formal/python/tools",
        "formal/output",
        "formal/tooling_snapshots",
        "scratch",
        "archive",
        "backup",
    }:
        assert root in text

    assert "Plain `pytest` and governance validation are read-only validation paths." in text
    assert "Existing large snapshots are not deleted or migrated by this policy." in text
    assert "TOE_ALLOW_TRACKED_OUTPUT_WRITES=1" in text


def test_repository_artifact_retention_policy_nonclaim_boundary() -> None:
    text = _read(POLICY_PATH)

    for forbidden_claim in {
        "master-action promotion",
        "pillar completion",
        "seam closure",
        "Phase 2 readiness",
        "empirical adequacy",
        "canonical ToE status",
        "QFT-GR source-map closure",
    }:
        assert forbidden_claim in text


def test_repository_artifact_retention_policy_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_repository_artifact_retention_policy_gate.py"
    )
