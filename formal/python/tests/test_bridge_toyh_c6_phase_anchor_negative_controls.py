from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyh_c6_phase_anchor import evaluate_toyh_c6_phase_anchor


def test_bridge_toyh_c6_phase_anchor_negative_control_amplitude_scaling() -> None:
    report = evaluate_toyh_c6_phase_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        amplitude_scale=1.1,
    )

    assert report["status"]["invariance_ok"] is False
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "FAIL_PHASE_INVARIANCE_TOL"


def test_bridge_toyh_c6_phase_anchor_negative_control_wrong_operator_sign() -> None:
    report = evaluate_toyh_c6_phase_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        anchor_sign=-1.0,
    )

    assert report["status"]["phase_anchor_ok"] is False
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "FAIL_ANCHOR_PHASE_MISMATCH"

