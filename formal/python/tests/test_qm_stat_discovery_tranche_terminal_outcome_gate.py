from __future__ import annotations

import json
from pathlib import Path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_qm_stat_discovery_tranche_terminal_outcome_gate() -> None:
    repo_root = _repo_root()
    tranche_path = repo_root / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_DISCRIMINATOR_TRANCHE_20260411_v0.json"
    queue_declaration_path = repo_root / "formal" / "docs" / "release" / "DISCOVERY_PRIORITY_QUEUE_20260411_v0.json"
    ruling_contract_path = repo_root / "formal" / "docs" / "release" / "DISCOVERY_TRANCHE_RULING_CONTRACT_20260411_v0.json"

    assert tranche_path.exists(), "QM-STAT discovery tranche declaration is missing."
    assert queue_declaration_path.exists(), "Discovery priority queue declaration is missing."
    assert ruling_contract_path.exists(), "Discovery tranche ruling contract is missing."

    tranche = _read_json(tranche_path)
    queue = _read_json(queue_declaration_path)
    ruling_contract = _read_json(ruling_contract_path)

    assert tranche.get("schema_id") == "QM_STAT_DISCOVERY_DISCRIMINATOR_TRANCHE_20260411_v0"
    assert tranche.get("target_row") == "ROW-SEAM-QM-STAT-001"
    assert tranche.get("blocker_class") == "SEAM_INTEGRATION_GAP"

    candidates = queue.get("candidates", [])
    assert isinstance(candidates, list) and candidates, "Discovery priority queue candidates must be non-empty."
    assert candidates[0].get("rank") == 1
    assert candidates[0].get("row_id") == tranche.get("target_row")

    allowed = ruling_contract.get("allowed_terminal_outcomes", [])
    assert isinstance(allowed, list) and allowed, "Ruling contract must define terminal outcomes."
    assert tranche.get("terminal_outcome") in allowed

    required_fields = ruling_contract.get("required_fields", {})
    for required_key in required_fields:
        assert tranche.get(required_key) not in (None, ""), f"Missing required tranche field: {required_key}"

    assert tranche.get("ruling_contract_pointer") == "formal/docs/release/DISCOVERY_TRANCHE_RULING_CONTRACT_20260411_v0.json"
