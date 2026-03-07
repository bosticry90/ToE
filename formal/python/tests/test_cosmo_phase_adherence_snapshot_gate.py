from __future__ import annotations

import json
import re
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
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _cosmo_roadmap_row(roadmap_text: str) -> tuple[str, str, str, str]:
    active_text, _ = split_active_and_archived(roadmap_text, ROADMAP_PATH)
    match = re.search(
        r"^\|\s*`PILLAR-COSMO`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]*)`\s*\|",
        active_text,
        flags=re.MULTILINE,
    )
    assert match is not None, "Missing active roadmap row for PILLAR-COSMO."
    return match.groups()


def test_cosmo_phase_adherence_snapshot_tokens_pinned() -> None:
    state_text = _read(STATE_PATH)
    required_tokens = [
        "COSMO_PHASE_ADHERENCE_SNAPSHOT_v0: CLOSED_HANDOFF_CROSS_SURFACE_SYNCED",
        "COSMO_PHASE_ADHERENCE_MATRIX_STATUS_v0: CLOSED",
        "COSMO_PHASE_ADHERENCE_ROADMAP_STATUS_v0: CLOSED",
        "COSMO_PHASE_ADHERENCE_REGISTRY_MODE_v0: CLOSED_HANDOFF",
        "COSMO_PHASE_ADHERENCE_PRIMARY_LANE_v0: TARGET-COSMO-BG-PLAN",
        "COSMO_PHASE_ADHERENCE_GOVERNANCE_SUITE_v0: INCLUDED",
        "formal/python/tests/test_cosmo_phase_adherence_snapshot_gate.py",
    ]
    missing = [token for token in required_tokens if token not in state_text]
    assert not missing, "COSMO phase adherence snapshot token drift: " + ", ".join(missing)


def test_cosmo_phase_adherence_cross_surface_alignment() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO")
    assert isinstance(cosmo, dict), "PILLAR-COSMO matrix row must exist."
    assert cosmo.get("matrix_status") == "CLOSED"
    assert cosmo.get("target_id") == "TARGET-COSMO-BG-PLAN"

    status, target_id, target_doc, prereqs = _cosmo_roadmap_row(_read(ROADMAP_PATH))
    assert status == "CLOSED"
    assert target_id == "TARGET-COSMO-BG-PLAN"
    assert target_doc == "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
    assert prereqs == "TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-SR-COV-PLAN"

    registry = _read_json(REGISTRY_PATH)
    rows = [row for row in registry.get("pillars", []) if row.get("pillar_id") == "PILLAR-COSMO"]
    assert len(rows) == 1, "PILLAR-COSMO registry row must exist exactly once."
    assert rows[0].get("mode") == "CLOSED_HANDOFF"
    assert rows[0].get("expected_matrix_status") == "CLOSED"


def test_cosmo_phase_adherence_gate_is_in_governance_suite() -> None:
    suite_text = _read(SUITE_PATH)
    gate_path = "formal/python/tests/test_cosmo_phase_adherence_snapshot_gate.py"
    assert gate_path in suite_text, "Governance suite must execute COSMO phase adherence snapshot gate."

