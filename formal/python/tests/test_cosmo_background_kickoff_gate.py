from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
COSMO_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_cosmo_target_contains_required_kickoff_tokens() -> None:
    text = _read(COSMO_TARGET_PATH)
    required_tokens = [
        "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0",
        "TARGET-COSMO-BG-PLAN",
        "COSMO_BACKGROUND_ADJUDICATION: DISCHARGED_v0_BOUNDED",
        "COSMO_BACKGROUND_SCOPE_BOUNDARY_v0: BACKGROUND_ONLY_NONCLAIM",
        "COSMO_PREREQS_v0: TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-SR-COV-PLAN",
        "COSMO_DELIVERABLE_METRIC_SURFACE_v0: BACKGROUND_METRIC_OBJECT_DECLARED",
        "COSMO_DELIVERABLE_EXPANSION_SURFACE_v0: HUBBLE_LIKE_OBJECT_DECLARED",
        "COSMO_DELIVERABLE_SOURCE_SURFACE_v0: EFFECTIVE_SOURCE_SECTOR_DECLARED",
        "COSMO_DELIVERABLE_REGIME_SURFACE_v0: DOMAIN_OF_VALIDITY_ASSUMPTIONS_DECLARED",
        "COSMO_DELIVERABLE_FALSIFIABILITY_SURFACE_v0: REGIME_LIMITS_AND_HOOKS_DECLARED",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "COSMO target is missing required kickoff token(s): " + ", ".join(missing)


def test_cosmo_roadmap_row_is_locked_and_points_to_target() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    match = re.search(
        r"^\|\s*`PILLAR-COSMO`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]*)`\s*\|",
        roadmap_text,
        flags=re.MULTILINE,
    )
    assert match is not None, "Missing roadmap row for PILLAR-COSMO."

    status, target_id, target_path, prereqs = match.groups()
    assert status == "CLOSED", "PILLAR-COSMO roadmap status must remain CLOSED."
    assert target_id == "TARGET-COSMO-BG-PLAN", "PILLAR-COSMO target ID drift detected in roadmap."
    assert target_path == "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md", (
        "PILLAR-COSMO authority target path drift detected in roadmap."
    )
    assert prereqs == "TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-SR-COV-PLAN", (
        "PILLAR-COSMO prerequisite set drift detected in roadmap."
    )


def test_state_handoff_points_to_cosmo_background_lane() -> None:
    state_text = _read(STATE_PATH)
    required_tokens = [
        "NEXT_PILLAR_FOCUS_v0: PILLAR-COSMO",
        "NEXT_PILLAR_PRIMARY_LANE_v0: TARGET-COSMO-BG-PLAN",
    ]
    missing = [token for token in required_tokens if token not in state_text]
    assert not missing, "State handoff is missing required COSMO lane token(s): " + ", ".join(missing)
