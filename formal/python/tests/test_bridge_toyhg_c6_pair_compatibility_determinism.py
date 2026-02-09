from __future__ import annotations

from formal.python.tools.bridge_toyhg_c6_pair_compatibility import (
    evaluate_toyhg_c6_pair_compatibility,
)


def test_bridge_toyhg_c6_pair_compatibility_deterministic() -> None:
    r1 = evaluate_toyhg_c6_pair_compatibility(
        toyh_phase_bridge_pass=True,
        toyh_current_bridge_pass=True,
        toyg_bridge_pass=True,
    )
    r2 = evaluate_toyhg_c6_pair_compatibility(
        toyh_phase_bridge_pass=True,
        toyh_current_bridge_pass=True,
        toyg_bridge_pass=True,
    )

    assert r1 == r2
    assert r1["schema_version"] == 1
    assert r1["observable_id"] == "TOYHG_C6_pair_compatibility_v1"


def test_bridge_toyhg_c6_pair_compatibility_accepts_uniform_pass_vector() -> None:
    report = evaluate_toyhg_c6_pair_compatibility(
        toyh_phase_bridge_pass=True,
        toyh_current_bridge_pass=True,
        toyg_bridge_pass=True,
    )
    assert report["status"]["admissible"] is True
    assert report["reason_code"] == "PASS_PAIR_COMPATIBLE"

