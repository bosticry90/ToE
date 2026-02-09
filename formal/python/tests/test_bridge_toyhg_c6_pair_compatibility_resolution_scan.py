from __future__ import annotations

from formal.python.tools.bridge_toyhg_c6_pair_compatibility import (
    evaluate_toyhg_c6_pair_compatibility,
)


def test_bridge_toyhg_c6_pair_compatibility_resolution_signature_map() -> None:
    cases = [
        ((True, True, True), True, "PASS_PAIR_COMPATIBLE"),
        ((False, False, False), True, "PASS_PAIR_COMPATIBLE"),
        ((False, False, True), False, "FAIL_PAIR_TOYG_MISMATCH"),
        ((True, False, True), False, "FAIL_PAIR_CURRENT_MISMATCH"),
        ((False, True, True), False, "FAIL_PAIR_PHASE_MISMATCH"),
        ((True, True, False), False, "FAIL_PAIR_TOYG_MISMATCH"),
    ]

    for (phase_pass, current_pass, toyg_pass), admissible, reason_code in cases:
        report = evaluate_toyhg_c6_pair_compatibility(
            toyh_phase_bridge_pass=phase_pass,
            toyh_current_bridge_pass=current_pass,
            toyg_bridge_pass=toyg_pass,
        )
        assert report["status"]["admissible"] is admissible
        assert report["reason_code"] == reason_code

