from __future__ import annotations

from pathlib import Path


def test_ct06_front_door_contract_is_pinned() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    contract_relpath = "formal/docs/ct06_external_anchor_dispersion_v0_front_door_contract.md"
    contract_path = repo_root / contract_relpath

    assert contract_path.exists(), f"Missing CT-06 front door contract: {contract_relpath}"

    text = contract_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-06",
        "external_anchor_dispersion_front_door_report",
        "Steinhauer2001_Fig3a_Digitized_v1",
        "ct06_reference_report.json",
        "ct06_candidate_report.json",
        "eps_rmse_kHz",
        "eps_max_abs_error_kHz",
        "eps_reduced_chi2",
        "alpha_scale_negative",
    ]
    for required in required_strings:
        assert required in text, f"CT-06 contract missing: {required}"

