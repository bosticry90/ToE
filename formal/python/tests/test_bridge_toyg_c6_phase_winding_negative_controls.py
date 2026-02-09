from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_phase_winding import evaluate_toyg_c6_phase_winding


def test_bridge_toyg_c6_phase_winding_negative_control_quantization_failure() -> None:
    report = evaluate_toyg_c6_phase_winding(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        winding_target=1.25,
        tol_winding=0.05,
        unwrap_margin=1e-6,
        amplitude_mod_eps=0.0,
    )

    assert report["status"]["unwrap_guard_ok"] is True
    assert report["status"]["integer_close"] is False
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "fail_not_integer_close"


def test_bridge_toyg_c6_phase_winding_negative_control_wrong_operator_sign() -> None:
    report = evaluate_toyg_c6_phase_winding(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        winding_target=1.0,
        tol_winding=0.05,
        unwrap_margin=1e-6,
        amplitude_mod_eps=0.0,
    )

    # Deliberately wrong operator: flip winding sign.
    wrong_winding = -float(report["metrics"]["raw_winding"])
    assert abs(wrong_winding - 1.0) > 0.5
