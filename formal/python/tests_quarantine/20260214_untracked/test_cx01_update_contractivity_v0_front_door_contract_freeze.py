from __future__ import annotations

from pathlib import Path


def test_cx01_front_door_contract_is_pinned() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    contract_relpath = "formal/docs/cx01_update_contractivity_v0_front_door_contract.md"
    contract_path = repo_root / contract_relpath

    assert contract_path.exists(), f"Missing CX-01 front door contract: {contract_relpath}"

    text = contract_path.read_text(encoding="utf-8")
    required_strings = [
        "CX-01",
        "update_contractivity_front_door_report",
        "cx01_reference_report.json",
        "cx01_candidate_report.json",
        "k_contract",
        "k_break",
        "eps_contractivity",
        "eps_break",
        "positive_control",
        "negative_control",
    ]
    for required in required_strings:
        assert required in text, f"CX-01 contract missing: {required}"
