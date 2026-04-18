from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
LEDGER_PATH = REPO_ROOT / "formal" / "output" / "empirical_packet05_decision_ledger_v0.json"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PACKET05_MATRIX_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_empirical_packet05_decision_ledger_parity_gate() -> None:
    ledger = _read_json(LEDGER_PATH)
    matrix = _read_json(MATRIX_PATH)

    assert ledger.get("ledger_id") == "empirical_packet05_decision_ledger_v0"
    assert set(ledger.get("rows", {})) == set(matrix.get("rows", {})) == {"GR", "SR"}

    for lane, row in matrix["rows"].items():
        artifact = _read_json(REPO_ROOT / row["artifact_path"])
        payload = artifact["payload"]
        lrow = ledger["rows"][lane]

        assert lrow["decision"] == payload["decision"]
        assert lrow["basis"] == payload["decision_basis"]
        assert lrow["decision_record_pointer"] == payload["decision_record_pointer"]
        assert lrow["falsification_surface_pointer"] == payload["falsification_surface_pointer"]
        assert (REPO_ROOT / row["decision_record_path"]).exists()
        assert (REPO_ROOT / row["falsification_surface_path"]).exists()
        if payload["decision"] != "INCONCLUSIVE_v0":
            assert lrow["guard"] == "PROTOCOL_COMPLIANT_INTERMEDIATE_TIER_OVERRIDE"
            assert (REPO_ROOT / row["override_criteria_path"]).exists()

    for text in (_read(ROADMAP_PATH), _read(STATE_PATH)):
        assert "formal/output/empirical_packet05_decision_ledger_v0.json" in text
        assert "formal/python/tests/test_empirical_packet05_decision_ledger_parity_gate.py" in text