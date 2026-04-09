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
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
REGISTRY_INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_registry_family_index_20260409_v0.json"
)
SEAM_INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "redundancy_control_seam_family_index_20260409_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _validate_family(family: dict) -> None:
    owner = family.get("canonical_owner")
    assert isinstance(owner, str) and owner
    assert (REPO_ROOT / owner).exists(), f"Canonical owner path must exist: {owner}"

    retention = family.get("retention_policy")
    assert retention == "ACTIVE_WINDOW_90_DAYS_THEN_ARCHIVE"

    archive_dest = family.get("archive_destination")
    assert isinstance(archive_dest, str) and archive_dest.startswith("archive/")
    assert (REPO_ROOT / archive_dest).exists(), f"Archive destination must exist: {archive_dest}"

    parity = family.get("parity_dependencies")
    assert isinstance(parity, list) and len(parity) >= 3
    for dep in parity:
        assert isinstance(dep, str) and dep
        assert (REPO_ROOT / dep).exists(), f"Parity dependency path must exist: {dep}"


def test_redundancy_control_admission_semantics() -> None:
    registry_payload = _json(REGISTRY_INDEX_PATH)
    seam_payload = _json(SEAM_INDEX_PATH)

    registry_families = registry_payload.get("families", [])
    seam_families = seam_payload.get("families", [])

    assert isinstance(registry_families, list) and registry_families
    assert isinstance(seam_families, list) and seam_families

    for family in registry_families + seam_families:
        _validate_family(family)

    all_ids = [str(f.get("family_id", "")) for f in registry_families + seam_families]
    assert all(all_ids), "All family entries must provide non-empty family_id."
    assert len(all_ids) == len(set(all_ids)), "Family ids must be unique across pilot indexes."


def test_redundancy_control_admission_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "REDUNDANCY_CONTROL_ADMISSION_SEMANTICS_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "REDUNDANCY_CONTROL_ADMISSION_SEMANTICS_RULE_v0: OWNER_AND_PARITY_PATHS_MUST_EXIST_PLUS_ARCHIVE_DESTINATION_MUST_EXIST_PLUS_RETENTION_POLICY_MUST_BE_ACTIVE_WINDOW_90_DAYS_THEN_ARCHIVE",
        "REDUNDANCY_CONTROL_ADMISSION_SEMANTICS_GATE_v0: formal/python/tests/test_redundancy_control_admission_semantics_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Canonical owner path exists for each pilot family? YES / NO",
        "Archive destination path exists for each pilot family? YES / NO",
        "Parity dependency paths exist for each pilot family? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"
