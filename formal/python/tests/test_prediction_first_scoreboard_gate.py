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
SCOREBOARD_PATH = REPO_ROOT / "formal" / "output" / "prediction_first_scoreboard_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "empirical_packet02_decision_ledger_v0.json"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CENTRAL_INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_prediction_first_scoreboard_surface() -> None:
    scoreboard = _read_json(SCOREBOARD_PATH)

    assert scoreboard.get("scoreboard_id") == "prediction_first_scoreboard_v0"
    assert scoreboard.get("status") == "ACTIVE_v0_NONCLAIM"
    assert set(scoreboard.get("decision_tokens", [])) == {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}


def test_prediction_first_scoreboard_matches_packet02_ledger() -> None:
    scoreboard = _read_json(SCOREBOARD_PATH)
    ledger = _read_json(LEDGER_PATH)
    matrix = _read_json(MATRIX_PATH)

    s_rows = scoreboard.get("rows", {})
    l_rows = ledger.get("rows", {})
    m_rows = matrix.get("rows", {})

    assert set(s_rows) == set(l_rows) == set(m_rows), "Scoreboard rows must match packet02 lane set."

    retain = prune = inconclusive = 0
    for lane in sorted(s_rows):
        s = s_rows[lane]
        l = l_rows[lane]
        decision = s.get("decision")

        assert decision == l.get("decision"), f"{lane}: scoreboard decision mismatch."
        assert s.get("decision_record_pointer") == l.get("decision_record_pointer"), (
            f"{lane}: scoreboard decision record pointer mismatch."
        )
        assert s.get("evidence_tier") in {"INTERMEDIATE_v0", "DISCHARGE_GRADE_v0"}

        artifact_pointer = s.get("artifact_pointer")
        assert isinstance(artifact_pointer, str) and artifact_pointer
        assert (REPO_ROOT / artifact_pointer).exists(), f"{lane}: missing artifact pointer `{artifact_pointer}`."

        if decision == "RETAIN_v0":
            retain += 1
        elif decision == "PRUNE_v0":
            prune += 1
        elif decision == "INCONCLUSIVE_v0":
            inconclusive += 1
        else:
            raise AssertionError(f"{lane}: unexpected decision `{decision}`")

    summary = scoreboard.get("summary", {})
    assert summary.get("total_lanes") == len(s_rows)
    assert summary.get("retain_count") == retain
    assert summary.get("prune_count") == prune
    assert summary.get("inconclusive_count") == inconclusive


def test_prediction_first_scoreboard_is_pinned() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    central_inventory_text = _read(CENTRAL_INVENTORY_PATH)

    for ref in (
        "formal/output/prediction_first_scoreboard_v0.json",
        "formal/docs/release/PREDICTION_FIRST_HYPOTHESIS_TEMPLATE_v0.md",
        "formal/docs/lanes/HYPOTHESIS_OV_DR_BR_PACKET02_v0.md",
        "formal/python/tests/test_prediction_first_scoreboard_gate.py",
    ):
        assert ref in roadmap_text
        # Transitional policy: references may be pinned in compact State or central inventory.
        assert (ref in state_text) or (ref in central_inventory_text)
