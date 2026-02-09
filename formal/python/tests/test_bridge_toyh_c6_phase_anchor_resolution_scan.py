from __future__ import annotations

from formal.python.tools.bridge_toyh_c6_phase_anchor import evaluate_toyh_c6_phase_anchor


def test_bridge_toyh_c6_phase_anchor_resolution_scan() -> None:
    for n in [7, 9, 11]:
        pass_report = evaluate_toyh_c6_phase_anchor(theta=1e-6, grid_n=n, tol_phase_anchor=1e-7)
        fail_report = evaluate_toyh_c6_phase_anchor(
            theta=1e-6,
            grid_n=n,
            tol_phase_anchor=1e-7,
            anchor_sign=-1.0,
        )

        assert pass_report["status"]["admissible"] is True
        assert pass_report["reason_code"] == "PASS_PHASE_ANCHOR"
        assert fail_report["status"]["admissible"] is False
        assert fail_report["reason_code"] == "FAIL_ANCHOR_PHASE_MISMATCH"

