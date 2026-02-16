from __future__ import annotations

from pathlib import Path


def test_ct07_front_door_contract_is_pinned() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    contract_relpath = "formal/docs/ct07_external_anchor_dispersion_lowk_slice_v0_front_door_contract.md"
    contract_path = repo_root / contract_relpath

    assert contract_path.exists(), f"Missing CT-07 front door contract: {contract_relpath}"

    text = contract_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-07",
        "external_anchor_dispersion_lowk_front_door_report",
        "ct07_reference_report.json",
        "ct07_candidate_report.json",
        "k_quantile",
        "k_max_um_inv",
        "c_s2_scale_negative",
        "non_independent_of_ct06",
    ]
    for required in required_strings:
        assert required in text, f"CT-07 contract missing: {required}"

