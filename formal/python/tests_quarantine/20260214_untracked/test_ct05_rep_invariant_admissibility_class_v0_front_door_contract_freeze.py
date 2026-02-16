from __future__ import annotations

from pathlib import Path


def test_ct05_front_door_contract_is_pinned() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    contract_relpath = "formal/docs/ct05_rep_invariant_admissibility_class_v0_front_door_contract.md"
    contract_path = repo_root / contract_relpath

    assert contract_path.exists(), f"Missing CT-05 front door contract: {contract_relpath}"

    text = contract_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-05",
        "rep_invariant_admissibility_class_front_door_report",
        "ct05_reference_report.json",
        "ct05_candidate_report.json",
        "rep_break_delta",
        "eps_rep_invariant",
        "eps_bound_residual",
    ]
    for required in required_strings:
        assert required in text, f"CT-05 contract missing: {required}"
