from __future__ import annotations

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
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _roadmap_token_value(token: str, roadmap_text: str) -> str:
    pattern = rf"{re.escape(token)}:\s*([A-Za-z0-9_\-,]+)"
    m = re.search(pattern, roadmap_text)
    assert m is not None, f"Missing roadmap token: {token}"
    return m.group(1)


def _result_status_for(row_id: str, results_text: str) -> str:
    pattern = rf"^\| {re.escape(row_id)} \| `([^`]+)` \|"
    m = re.search(pattern, results_text, flags=re.MULTILINE)
    assert m is not None, f"Missing result row: {row_id}"
    return m.group(1)


def _pillars_with_physics_status(roadmap_text: str) -> list[str]:
    return sorted(set(re.findall(r"PILLAR-([A-Z0-9]+)_PHYSICS_STATUS:", roadmap_text)))


def _required_closure_rows(pillar: str, roadmap_text: str) -> list[str]:
    token = f"REQUIRED_{pillar}_CLOSURE_ROWS"
    m = re.search(rf"{re.escape(token)}:\s*([A-Za-z0-9,\-_]+)", roadmap_text)
    if m is None:
        return []
    return [row.strip() for row in m.group(1).split(",") if row.strip()]


def test_dual_layer_terminology_tokens_are_present() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    required_phrases = [
        "`PHYSICS-CLOSED`",
        "`GOVERNANCE-CLOSED`",
        "`MATRIX-CLOSED`",
        "Conversational `closed` defaults to `PHYSICS-CLOSED`",
    ]
    for phrase in required_phrases:
        assert phrase in roadmap_text, f"Missing dual-layer terminology phrase: {phrase}"


def test_each_declared_pillar_dual_layer_has_all_gate_tokens() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    pillars = _pillars_with_physics_status(roadmap_text)
    assert pillars, "Expected at least one pillar dual-layer status token in roadmap."
    for pillar in pillars:
        _ = _roadmap_token_value(f"PILLAR-{pillar}_PHYSICS_STATUS", roadmap_text)
        _ = _roadmap_token_value(f"PILLAR-{pillar}_GOVERNANCE_STATUS", roadmap_text)
        _ = _roadmap_token_value(f"PROCEED_GATE_{pillar}", roadmap_text)
        _ = _roadmap_token_value(f"MATRIX_CLOSURE_GATE_{pillar}", roadmap_text)


def test_each_declared_pillar_proceed_gate_requires_physics_closed() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    for pillar in _pillars_with_physics_status(roadmap_text):
        physics_status = _roadmap_token_value(f"PILLAR-{pillar}_PHYSICS_STATUS", roadmap_text)
        proceed_gate = _roadmap_token_value(f"PROCEED_GATE_{pillar}", roadmap_text)
        if proceed_gate.startswith("ALLOWED_"):
            assert physics_status.startswith("CLOSED_"), (
                f"Proceed gate for {pillar} is ALLOWED but PHYSICS status is not CLOSED."
            )


def test_each_declared_pillar_matrix_gate_requires_governance_closed_and_rows_non_blocked() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    results_text = _read(RESULTS_PATH)
    for pillar in _pillars_with_physics_status(roadmap_text):
        governance_status = _roadmap_token_value(f"PILLAR-{pillar}_GOVERNANCE_STATUS", roadmap_text)
        matrix_gate = _roadmap_token_value(f"MATRIX_CLOSURE_GATE_{pillar}", roadmap_text)
        required_rows = _required_closure_rows(pillar, roadmap_text)
        blocked_required_rows = [
            row_id for row_id in required_rows if _result_status_for(row_id, results_text).startswith("B-")
        ]
        if matrix_gate.startswith("ALLOWED_"):
            assert governance_status.startswith("CLOSED_"), (
                f"Matrix closure gate for {pillar} is ALLOWED but governance status is not CLOSED."
            )
            assert not blocked_required_rows, (
                f"Matrix closure gate for {pillar} is ALLOWED while required rows remain blocked: "
                + ", ".join(blocked_required_rows)
            )
