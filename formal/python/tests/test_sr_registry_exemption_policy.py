from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_DISCHARGE_REGISTRY_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
SR_ROADMAP_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"
)

SR_EXEMPTION_TOKEN = (
    "PILLAR-SR_REGISTRY_EXEMPTION_v0: SR_CLOSURE_NOT_TRACKED_IN_GENERIC_REGISTRY"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_sr_registry_coverage_is_explicitly_enforced() -> None:
    registry = json.loads(_read(REGISTRY_PATH))
    pillars = registry.get("pillars", [])
    pillar_keys = {entry.get("pillar_key") for entry in pillars if isinstance(entry, dict)}
    sr_in_registry = "SR" in pillar_keys

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    sr_roadmap_text = _read(SR_ROADMAP_PATH)

    if sr_in_registry:
        return

    assert SR_EXEMPTION_TOKEN in roadmap_text, (
        "SR is absent from PILLAR_DISCHARGE_REGISTRY_v0.json, so roadmap must pin the "
        "SR registry-exemption token."
    )
    assert SR_EXEMPTION_TOKEN in state_text, (
        "SR is absent from PILLAR_DISCHARGE_REGISTRY_v0.json, so State_of_the_Theory.md must pin the "
        "SR registry-exemption token."
    )
    assert SR_EXEMPTION_TOKEN in sr_roadmap_text, (
        "SR is absent from PILLAR_DISCHARGE_REGISTRY_v0.json, so the SR full-derivation enforcement roadmap "
        "must pin the SR registry-exemption token."
    )

