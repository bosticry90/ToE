from __future__ import annotations

import json
from pathlib import Path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_gr_discovery_tranche_terminal_outcome_gate() -> None:
    repo_root = _repo_root()
    tranche_path = repo_root / "formal" / "docs" / "release" / "GR_DISCOVERY_DISCRIMINATOR_TRANCHE_20260411_v0.json"
    rescoring_path = repo_root / "formal" / "output" / "reports" / "discovery_queue_rescoring_pass_report_20260411_v0.json"
    ruling_contract_path = repo_root / "formal" / "docs" / "release" / "DISCOVERY_TRANCHE_RULING_CONTRACT_20260411_v0.json"

    assert tranche_path.exists(), "GR discovery tranche declaration is missing."
    assert rescoring_path.exists(), "Discovery queue rescoring pass report is missing."
    assert ruling_contract_path.exists(), "Discovery tranche ruling contract is missing."

    tranche = _read_json(tranche_path)
    rescoring = _read_json(rescoring_path)
    ruling_contract = _read_json(ruling_contract_path)

    assert tranche.get("schema_id") == "GR_DISCOVERY_DISCRIMINATOR_TRANCHE_20260411_v0"
    assert tranche.get("target_row") == "ROW-PILLAR-GR-001"
    assert tranche.get("blocker_class") == "THEOREM_GAP"
    assert tranche.get("bounded_execution_policy", {}).get("probe_lane_enabled") is False

    rescoring_summary = rescoring.get("summary", {})
    assert rescoring_summary.get("selected_next_route") == "ACTIVATE_NEXT_RANKED_SEAM"
    assert rescoring_summary.get("rank3_candidate") == tranche.get("target_row")

    allowed = ruling_contract.get("allowed_terminal_outcomes", [])
    assert isinstance(allowed, list) and allowed, "Ruling contract must define terminal outcomes."
    assert tranche.get("terminal_outcome") in allowed

    required_fields = ruling_contract.get("required_fields", {})
    for required_key in required_fields:
        assert tranche.get(required_key) not in (None, ""), f"Missing required tranche field: {required_key}"

    assert tranche.get("ruling_contract_pointer") == "formal/docs/release/DISCOVERY_TRANCHE_RULING_CONTRACT_20260411_v0.json"
