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
CHECKPOINT_MD = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "WS_10_TGC_83_QFT_THEOREM_GAP_CLOSURE_INCREMENT_EXECUTION_CHECKPOINT_20260410_v0.md"
)
CHECKPOINT_JSON = (
    REPO_ROOT
    / "formal"
    / "output"
    / "ws10_tgc83_qft_theorem_gap_closure_increment_execution_checkpoint_20260410_v0.json"
)
EXPECTED_GATE_EVIDENCE = (
    "governance_gate.ok row=ROW-PILLAR-QFT-001 blocker=THEOREM_GAP "
    "declaration=formal/docs/release/TGC_83_DECLARATION.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_tgc83_checkpoint_contains_row_correct_governance_evidence() -> None:
    text = _read(CHECKPOINT_MD)
    assert EXPECTED_GATE_EVIDENCE in text


def test_tgc83_checkpoint_json_pins_qft_contract() -> None:
    payload = _json(CHECKPOINT_JSON)

    assert payload.get("tranche_id") == "TGC-83"
    assert payload.get("target_row") == "ROW-PILLAR-QFT-001"
    assert payload.get("blocker_class") == "THEOREM_GAP"
    assert payload.get("declaration_path") == "formal/docs/release/TGC_83_DECLARATION.md"

    verification = payload.get("verification", {})
    governance_evidence = verification.get("governance_gate_evidence", [])
    assert EXPECTED_GATE_EVIDENCE in governance_evidence
