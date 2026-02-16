from __future__ import annotations

from pathlib import Path


def test_ct09_front_door_contract_is_pinned() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    contract_relpath = "formal/docs/ct09_independent_external_anchor_sound_speed_v0_front_door_contract.md"
    contract_path = repo_root / contract_relpath

    assert contract_path.exists(), f"Missing CT-09 front door contract: {contract_relpath}"

    text = contract_path.read_text(encoding="utf-8")
    required_strings = [
        "CT-09",
        "independent_external_anchor_sound_speed_front_door_report",
        "ct09_reference_report.json",
        "ct09_candidate_report.json",
        "distance_um_vs_time_ms",
        "c_scale_negative",
        "eps_rmse_um",
        "eps_max_abs_error_um",
        "eps_reduced_chi2",
        "semantically binding",
    ]
    for required in required_strings:
        assert required in text, f"CT-09 contract missing: {required}"
