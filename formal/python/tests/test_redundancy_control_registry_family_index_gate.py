from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_registry_family_index_20260409_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_redundancy_control_registry_family_index_shape() -> None:
    payload = _json(INDEX_PATH)

    assert payload.get("schema_id") == "REDUNDANCY_CONTROL_REGISTRY_FAMILY_INDEX_20260409_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM_PILOT"
    assert payload.get("pilot_scope") == "ONE_REGISTRY_FAMILY"
    assert payload.get("admission_rule") == (
        "MISSING_OWNER_OR_RETENTION_OR_ARCHIVE_OR_PARITY_DEPENDENCIES_IS_HARD_FAIL"
    )

    families = payload.get("families")
    assert isinstance(families, list)
    assert len(families) == 1

    family = families[0]
    assert family.get("family_id") == "TOE_MASTER_ACTION_SEAM_REGISTRY"
    assert isinstance(family.get("canonical_owner"), str) and family["canonical_owner"]
    assert isinstance(family.get("retention_policy"), str) and family["retention_policy"]
    assert isinstance(family.get("archive_destination"), str) and family["archive_destination"]

    parity_deps = family.get("parity_dependencies")
    assert isinstance(parity_deps, list)
    assert len(parity_deps) >= 3


def test_redundancy_control_registry_family_index_state_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)

    required = [
        "REDUNDANCY_CONTROL_REGISTRY_PILOT_STATUS_v0: ACTIVE_ONE_FAMILY_NONLIVE_NONCLAIM",
        "REDUNDANCY_CONTROL_REGISTRY_PILOT_INDEX_v0: formal/output/reports/redundancy_control_registry_family_index_20260409_v0.json",
        "REDUNDANCY_CONTROL_REGISTRY_PILOT_RULE_v0: MISSING_OWNER_OR_RETENTION_OR_ARCHIVE_OR_PARITY_DEPENDENCIES_IS_HARD_FAIL",
        "REDUNDANCY_CONTROL_REGISTRY_PILOT_GATE_v0: formal/python/tests/test_redundancy_control_registry_family_index_gate.py",
    ]
    for token in required:
        assert token in state_text, f"Missing state token: {token}"
