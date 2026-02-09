from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyh_c6_current_anchor import evaluate_toyh_c6_current_anchor


def test_bridge_toyh_c6_current_anchor_negative_control_zero_alpha_response_min() -> None:
    report = evaluate_toyh_c6_current_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        local_phase_shear_alpha=0.0,
        min_anchor_response=1e-8,
    )
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "FAIL_CURRENT_ANCHOR_RESPONSE_MIN"


def test_bridge_toyh_c6_current_anchor_negative_control_amplitude_scaling() -> None:
    report = evaluate_toyh_c6_current_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        amplitude_scale=1.1,
        local_phase_shear_alpha=0.5,
    )
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "FAIL_CURRENT_INVARIANCE_TOL"


def test_bridge_toyh_c6_current_anchor_negative_control_wrong_operator_sign() -> None:
    report = evaluate_toyh_c6_current_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        local_phase_shear_alpha=1e-6,
        anchor_sign=-1.0,
    )
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "FAIL_CURRENT_ANCHOR_MISMATCH"

