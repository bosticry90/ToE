from __future__ import annotations

import json
from pathlib import Path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_qft_gr_discovery_tranche_terminal_outcome_gate() -> None:
    repo_root = _repo_root()
    tranche_path = repo_root / "formal" / "docs" / "release" / "QFT_GR_DISCOVERY_DISCRIMINATOR_TRANCHE_20260411_v0.json"
    route_decision_path = repo_root / "formal" / "output" / "reports" / "qm_stat_discovery_next_route_decision_report_20260411_v0.json"
    ruling_contract_path = repo_root / "formal" / "docs" / "release" / "DISCOVERY_TRANCHE_RULING_CONTRACT_20260411_v0.json"

    assert tranche_path.exists(), "QFT-GR discovery tranche declaration is missing."
    assert route_decision_path.exists(), "QM-STAT next-route decision report is missing."
    assert ruling_contract_path.exists(), "Discovery tranche ruling contract is missing."

    tranche = _read_json(tranche_path)
    route_decision = _read_json(route_decision_path)
    ruling_contract = _read_json(ruling_contract_path)

    assert tranche.get("schema_id") == "QFT_GR_DISCOVERY_DISCRIMINATOR_TRANCHE_20260411_v0"
    assert tranche.get("target_row") == "ROW-SEAM-QFT-GR-001"
    assert tranche.get("blocker_class") == "SEAM_INTEGRATION_GAP"
    assert tranche.get("bounded_execution_policy", {}).get("probe_lane_enabled") is False

    route_summary = route_decision.get("summary", {})
    assert route_summary.get("selected_route_id") == "ACTIVATE_NEXT_RANKED_SEAM"
    assert route_summary.get("next_ranked_row_id") == tranche.get("target_row")

    allowed = ruling_contract.get("allowed_terminal_outcomes", [])
    assert isinstance(allowed, list) and allowed, "Ruling contract must define terminal outcomes."
    assert tranche.get("terminal_outcome") in allowed

    required_fields = ruling_contract.get("required_fields", {})
    for required_key in required_fields:
        assert tranche.get(required_key) not in (None, ""), f"Missing required tranche field: {required_key}"

    assert tranche.get("ruling_contract_pointer") == "formal/docs/release/DISCOVERY_TRANCHE_RULING_CONTRACT_20260411_v0.json"