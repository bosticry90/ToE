from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
CHECKLIST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_CLOSURE_PREP_CHECKLIST_v0.md"

EXPECTED_TOKENS = {
    "PILLAR-STAT_PHYSICS_STATUS": "OPEN_v0_ACTIVE_PREEXECUTION",
    "PILLAR-STAT_GOVERNANCE_STATUS": "OPEN_v0_REQUIRED_ROWS_BLOCKED_EXECUTION",
    "PROCEED_GATE_STAT": "BLOCKED_v0_PHYSICS_NOT_CLOSED",
    "MATRIX_CLOSURE_GATE_STAT": "BLOCKED_v0_GOVERNANCE_NOT_CLOSED",
    "REQUIRED_STAT_CLOSURE_ROWS": "TOE-STAT-DER-01,TOE-STAT-DER-02",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_,-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_checklist_token(text: str, token_name: str) -> str:
    m = re.search(rf"`{re.escape(token_name)}:\s*([A-Za-z0-9_,-]+)`", text)
    assert m is not None, f"Missing checklist token mirror `{token_name}`."
    return m.group(1)


def _results_status(text: str, row_id: str) -> str:
    m = re.search(rf"^\|\s*{re.escape(row_id)}\s*\|\s*`([^`]+)`\s*\|", text, flags=re.MULTILINE)
    assert m is not None, f"Missing result row `{row_id}`."
    return m.group(1)


def test_stat_dual_closure_tokens_are_mirrored_across_canonical_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    for token_name in EXPECTED_TOKENS:
        roadmap_value = _extract_token(roadmap_text, token_name)
        state_value = _extract_token(state_text, token_name)
        checklist_value = _extract_checklist_token(checklist_text, token_name)
        assert roadmap_value == state_value, f"{token_name} must be mirrored between roadmap and state."
        assert roadmap_value == checklist_value, f"{token_name} must be mirrored between roadmap and checklist."


def test_stat_dual_closure_posture_matches_matrix_and_gate_tokens() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    results_text = _read(RESULTS_PATH)

    row_match = re.search(r"^\|\s*`PILLAR-STAT`\s*\|\s*`([^`]+)`\s*\|", roadmap_text, flags=re.MULTILINE)
    assert row_match is not None, "Missing roadmap row for PILLAR-STAT."
    roadmap_status = row_match.group(1)
    assert roadmap_status in {"ACTIVE", "CLOSED"}, "PILLAR-STAT roadmap row must be ACTIVE or CLOSED."

    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist."
    matrix_status = stat_matrix.get("matrix_status")
    assert matrix_status in {"ACTIVE", "CLOSED"}, "PILLAR-STAT matrix status must be ACTIVE or CLOSED."
    if roadmap_status == "CLOSED":
        assert matrix_status == "CLOSED", "CLOSED roadmap posture must mirror CLOSED matrix posture for PILLAR-STAT."
    else:
        assert matrix_status in {"ACTIVE", "CLOSED"}, (
            "ACTIVE roadmap posture may run with staged CLOSED matrix handoff or fully ACTIVE matrix ownership."
        )

    full_derivation = str(stat_matrix.get("full_derivation", ""))
    inevitability = str(stat_matrix.get("inevitability", ""))
    physics_status = _extract_token(roadmap_text, "PILLAR-STAT_PHYSICS_STATUS")
    governance_status = _extract_token(roadmap_text, "PILLAR-STAT_GOVERNANCE_STATUS")
    proceed_gate = _extract_token(roadmap_text, "PROCEED_GATE_STAT")
    matrix_gate = _extract_token(roadmap_text, "MATRIX_CLOSURE_GATE_STAT")
    rows = [row.strip() for row in _extract_token(roadmap_text, "REQUIRED_STAT_CLOSURE_ROWS").split(",") if row.strip()]

    for row_id in rows:
        status = _results_status(results_text, row_id)
        if matrix_status == "ACTIVE":
            assert status.startswith("B-"), (
                f"STAT pre-discharge row `{row_id}` must remain B-* blocked before closure; found `{status}`."
            )
        else:
            assert not status.startswith("B-"), (
                f"STAT discharged row `{row_id}` must be non-B-* after closure; found `{status}`."
            )

    if matrix_status == "ACTIVE":
        assert full_derivation == "NOT_YET_DISCHARGED"
        assert inevitability == "NOT_YET_DISCHARGED"
        assert physics_status.startswith("OPEN_")
        assert governance_status.startswith("OPEN_")
        assert proceed_gate.startswith("BLOCKED_")
        assert matrix_gate.startswith("BLOCKED_")
    else:
        assert full_derivation.startswith("DISCHARGED")
        assert inevitability.startswith("DISCHARGED")
        assert physics_status.startswith("CLOSED_")
        assert governance_status.startswith("CLOSED_")
        assert proceed_gate.startswith("ALLOWED_")
        assert matrix_gate.startswith("ALLOWED_")


def test_stat_required_closure_rows_remain_blocked_execution_rows() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    results_text = _read(RESULTS_PATH)

    rows = [row.strip() for row in _extract_token(roadmap_text, "REQUIRED_STAT_CLOSURE_ROWS").split(",") if row.strip()]
    assert rows == ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]

    matrix = _read_json(MATRIX_PATH)
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist."
    matrix_status = stat_matrix.get("matrix_status")
    assert matrix_status in {"ACTIVE", "CLOSED"}

    for row_id in rows:
        status = _results_status(results_text, row_id)
        if matrix_status == "ACTIVE":
            assert status.startswith("B-"), (
                f"STAT closure-prep row `{row_id}` must remain B-* blocked before full closure; found `{status}`."
            )
        else:
            assert not status.startswith("B-"), (
                f"STAT discharged row `{row_id}` must be non-B-* after closure; found `{status}`."
            )


def test_stat_blocked_closure_gates_remain_consistent_with_open_statuses() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist."
    matrix_status = stat_matrix.get("matrix_status")
    assert matrix_status in {"ACTIVE", "CLOSED"}

    physics_status = _extract_token(roadmap_text, "PILLAR-STAT_PHYSICS_STATUS")
    governance_status = _extract_token(roadmap_text, "PILLAR-STAT_GOVERNANCE_STATUS")
    proceed_gate = _extract_token(roadmap_text, "PROCEED_GATE_STAT")
    matrix_gate = _extract_token(roadmap_text, "MATRIX_CLOSURE_GATE_STAT")

    if matrix_status == "ACTIVE":
        assert physics_status.startswith("OPEN_")
        assert governance_status.startswith("OPEN_")
        assert proceed_gate.startswith("BLOCKED_")
        assert matrix_gate.startswith("BLOCKED_")
    else:
        assert physics_status.startswith("CLOSED_")
        assert governance_status.startswith("CLOSED_")
        assert proceed_gate.startswith("ALLOWED_")
        assert matrix_gate.startswith("ALLOWED_")
