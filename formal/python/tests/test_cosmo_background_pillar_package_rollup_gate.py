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
COSMO_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
)
COSMO_SUMMARY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md"
COSMO_PACKAGE_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "COSMO_BACKGROUND_PILLAR_PACKAGE_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_cosmo_rollup_artifacts_exist() -> None:
    assert COSMO_TARGET_PATH.exists(), "Missing COSMO parent target document."
    assert COSMO_SUMMARY_PATH.exists(), "Missing COSMO pillar summary document."
    assert COSMO_PACKAGE_PATH.exists(), "Missing COSMO pillar package policy document."


def test_cosmo_summary_contains_required_rollup_tokens() -> None:
    text = _read(COSMO_SUMMARY_PATH)
    required_tokens = [
        "TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0",
        "COSMO_BACKGROUND_ADJUDICATION: NOT_YET_DISCHARGED",
        "COSMO_BG_MICRO01_PROGRESS_v0: OBJECT_SURFACE_TOKEN_PINNED",
        "COSMO_BG_MICRO02_PROGRESS_v0: EXPANSION_LAW_SURFACE_TOKEN_PINNED",
        "COSMO_BG_MICRO03_PROGRESS_v0: SOURCE_COUPLING_SURFACE_TOKEN_PINNED",
        "COSMO_BG_MICRO04_PROGRESS_v0: REGIME_FALSIFIABILITY_SURFACE_TOKEN_PINNED",
        "COSMO_BG_MICRO05_PROGRESS_v0: PACKAGE_FREEZE_REOPEN_POLICY_TOKEN_PINNED",
        "COSMO_BG_MICRO05_PACKAGE_FREEZE_STATUS_v0: FROZEN_CONTENTS_PINNED",
        "COSMO_BG_MICRO05_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "Known limitations",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO summary missing required token(s): " + ", ".join(missing)


def test_cosmo_package_contains_required_freeze_and_reopen_tokens() -> None:
    text = _read(COSMO_PACKAGE_PATH)
    required_tokens = [
        "COSMO_BACKGROUND_PILLAR_PACKAGE_v0",
        "COSMO_BACKGROUND_PILLAR_PACKAGE_STATUS_v0: FROZEN_CONTENTS_PINNED",
        "COSMO_BACKGROUND_PILLAR_PACKAGE_PROGRESS_v0: REQUIRED_CONTENTS_PINNED",
        "COSMO_BACKGROUND_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "REOPEN_TRIGGER_COSMO_SURFACE_DRIFT_v0",
        "REOPEN_TRIGGER_COSMO_SCOPE_BOUNDARY_REGRESSION_v0",
        "REOPEN_TRIGGER_COSMO_PACKAGE_CONTENT_MISMATCH_v0",
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md",
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_01_OBJECT_SURFACE_v0.md",
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_02_EXPANSION_LAW_SURFACE_v0.md",
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_03_SOURCE_COUPLING_SURFACE_v0.md",
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_04_REGIME_FALSIFIABILITY_SURFACE_v0.md",
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_05_PACKAGE_FREEZE_REOPEN_POLICY_v0.md",
        "TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md",
        "cosmo_bg_micro01_object_surface_cycle01_v0.json",
        "cosmo_bg_micro02_expansion_law_surface_cycle01_v0.json",
        "cosmo_bg_micro03_source_coupling_surface_cycle01_v0.json",
        "cosmo_bg_micro04_regime_falsifiability_surface_cycle01_v0.json",
        "cosmo_bg_micro05_package_freeze_reopen_policy_cycle01_v0.json",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO package missing required token(s): " + ", ".join(missing)


def test_cosmo_target_references_rollup_surfaces_and_gate() -> None:
    text = _read(COSMO_TARGET_PATH)
    required_tokens = [
        "formal/docs/paper/TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md",
        "formal/markdown/locks/policy/COSMO_BACKGROUND_PILLAR_PACKAGE_v0.md",
        "formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO target missing rollup pointer token(s): " + ", ".join(missing)
