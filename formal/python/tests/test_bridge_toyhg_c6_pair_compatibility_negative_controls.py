from __future__ import annotations

from formal.python.tools.bridge_toyhg_c6_pair_compatibility import (
    evaluate_toyhg_c6_pair_compatibility,
)


def test_bridge_toyhg_c6_pair_compatibility_negative_control_phase_current_vs_toyg() -> None:
    report = evaluate_toyhg_c6_pair_compatibility(
        toyh_phase_bridge_pass=False,
        toyh_current_bridge_pass=False,
        toyg_bridge_pass=True,
    )
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "FAIL_PAIR_TOYG_MISMATCH"
    assert report["status"]["localization_note"] == "toyg_bridge_channel"


def test_bridge_toyhg_c6_pair_compatibility_negative_control_current_only() -> None:
    report = evaluate_toyhg_c6_pair_compatibility(
        toyh_phase_bridge_pass=True,
        toyh_current_bridge_pass=False,
        toyg_bridge_pass=True,
    )
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "FAIL_PAIR_CURRENT_MISMATCH"
    assert report["status"]["localization_note"] == "toyh_current_channel"


def test_bridge_toyhg_c6_pair_compatibility_negative_control_toyg_only() -> None:
    report = evaluate_toyhg_c6_pair_compatibility(
        toyh_phase_bridge_pass=True,
        toyh_current_bridge_pass=True,
        toyg_bridge_pass=False,
    )
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "FAIL_PAIR_TOYG_MISMATCH"
    assert report["status"]["localization_note"] == "toyg_bridge_channel"

