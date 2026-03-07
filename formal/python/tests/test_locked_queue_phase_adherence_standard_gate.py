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
STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOCKED_QUEUE_PHASE_ADHERENCE_STANDARD_v0.md"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _roadmap_row(roadmap_text: str, pillar_id: str) -> tuple[str, str, str, str]:
    active_text, _ = split_active_and_archived(roadmap_text, ROADMAP_PATH)
    pattern = (
        rf"^\|\s*`{re.escape(pillar_id)}`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|"
        rf"\s*`([^`]+)`\s*\|\s*`([^`]*)`\s*\|"
    )
    match = re.search(pattern, active_text, flags=re.MULTILINE)
    assert match is not None, f"Missing active roadmap row for {pillar_id}."
    return match.groups()


def _state_snapshot_tokens(prefix: str, target_id: str) -> list[str]:
    return [
        f"{prefix}_PHASE_ADHERENCE_SNAPSHOT_v0: LOCKED_QUEUE_CROSS_SURFACE_SYNCED",
        f"{prefix}_PHASE_ADHERENCE_MATRIX_STATUS_v0: LOCKED",
        f"{prefix}_PHASE_ADHERENCE_ROADMAP_STATUS_v0: LOCKED",
        f"{prefix}_PHASE_ADHERENCE_REGISTRY_MODE_v0: LOCKED_QUEUE",
        f"{prefix}_PHASE_ADHERENCE_PRIMARY_LANE_v0: {target_id}",
        f"{prefix}_PHASE_ADHERENCE_GOVERNANCE_SUITE_v0: INCLUDED",
    ]


def test_locked_queue_standard_artifacts_and_suite_wiring() -> None:
    standard_text = _read(STANDARD_PATH)
    required_doc_tokens = [
        "LOCKED_QUEUE_PHASE_ADHERENCE_STANDARD_v0",
        "formal/python/tests/test_locked_queue_phase_adherence_standard_gate.py",
        "formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json",
        "formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json",
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "State_of_the_Theory.md",
    ]
    missing_doc = [token for token in required_doc_tokens if token not in standard_text]
    assert not missing_doc, "Locked-queue standard doc drift: " + ", ".join(missing_doc)

    suite_text = _read(SUITE_PATH)
    gate_path = "formal/python/tests/test_locked_queue_phase_adherence_standard_gate.py"
    assert gate_path in suite_text, "Governance suite must execute locked-queue phase adherence standard gate."


def test_all_locked_queue_rows_have_state_snapshot_and_cross_surface_lock_alignment() -> None:
    registry = _read_json(REGISTRY_PATH)
    matrix = _read_json(MATRIX_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    locked_rows = [row for row in registry.get("pillars", []) if row.get("mode") == "LOCKED_QUEUE"]
    if not locked_rows:
        return

    for row in locked_rows:
        pillar_id = row.get("pillar_id")
        assert isinstance(pillar_id, str) and pillar_id.startswith("PILLAR-"), "Invalid locked-queue pillar id in registry."

        target_id = row.get("target_id")
        assert isinstance(target_id, str) and target_id, f"{pillar_id} must define a non-empty target_id in registry."

        matrix_row = matrix.get("pillars", {}).get(pillar_id)
        assert isinstance(matrix_row, dict), f"{pillar_id} must exist in pillar status matrix."
        matrix_status = matrix_row.get("matrix_status")
        assert matrix_status in {"LOCKED", "CLOSED"}, f"{pillar_id} matrix status must be LOCKED or CLOSED."
        assert matrix_row.get("target_id") == target_id, f"{pillar_id} target_id must match matrix row target_id."

        roadmap_status, roadmap_target_id, roadmap_target_doc, roadmap_prereqs = _roadmap_row(roadmap_text, pillar_id)
        assert roadmap_status == matrix_status, f"{pillar_id} roadmap status must match matrix status."
        assert roadmap_target_id == target_id, f"{pillar_id} target_id must match roadmap row target_id."

        matrix_target_doc = matrix_row.get("target_doc")
        if isinstance(matrix_target_doc, str) and matrix_target_doc:
            assert roadmap_target_doc == matrix_target_doc, f"{pillar_id} roadmap target_doc must match matrix target_doc."

        prereq_list = row.get("prerequisites", [])
        if isinstance(prereq_list, list) and prereq_list:
            prereq_joined = ";".join(prereq_list)
            assert roadmap_prereqs == prereq_joined, f"{pillar_id} roadmap prereqs must match registry prerequisites."

        prefix = pillar_id.removeprefix("PILLAR-").replace("-", "_")
        if matrix_status == "LOCKED":
            required_state_tokens = _state_snapshot_tokens(prefix, target_id)
            missing_state_tokens = [token for token in required_state_tokens if token not in state_text]
            assert not missing_state_tokens, (
                f"{pillar_id} missing locked-queue snapshot token(s) in state: " + ", ".join(missing_state_tokens)
            )