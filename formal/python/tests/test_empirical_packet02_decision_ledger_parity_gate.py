from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "empirical_packet02_decision_ledger_v0.json"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET02_MATRIX_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_empirical_packet02_decision_ledger_parity_gate() -> None:
    ledger = _read_json(LEDGER_PATH)
    matrix = _read_json(MATRIX_PATH)

    assert ledger.get("ledger_id") == "empirical_packet02_decision_ledger_v0"
    assert ledger.get("ledger_version") == 1

    ledger_rows = ledger.get("rows", {})
    matrix_rows = matrix.get("rows", {})
    assert isinstance(ledger_rows, dict) and isinstance(matrix_rows, dict)
    assert set(ledger_rows) == set(matrix_rows)

    for lane, row in matrix_rows.items():
        artifact = _read_json(REPO_ROOT / row["artifact_path"])
        payload = artifact.get("payload", {})
        lrow = ledger_rows[lane]

        assert lrow.get("decision") == payload.get("decision")
        assert lrow.get("basis") == payload.get("decision_basis")
        assert lrow.get("decision_record_pointer") == payload.get("decision_record_pointer")
        assert lrow.get("guard") == "PROTOCOL_COMPLIANT_INTERMEDIATE_TIER"
        assert (REPO_ROOT / lrow["decision_record_pointer"]).exists()

    roadmap = _read(ROADMAP_PATH)
    state = _read(STATE_PATH)
    for ref in (
        "formal/output/empirical_packet02_decision_ledger_v0.json",
        "formal/python/tests/test_empirical_packet02_decision_ledger_parity_gate.py",
    ):
        assert ref in roadmap
        assert ref in state
