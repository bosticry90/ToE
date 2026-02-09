from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_mode_index_quantization import (
    evaluate_toyg_c6_mode_index_quantization,
)


def test_bridge_toyg_c6_mode_index_quantization_negative_control_integer_closeness_failure() -> None:
    report = evaluate_toyg_c6_mode_index_quantization(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        mode_target=1.25,
        tol_mode=0.1,
        min_peak_fraction=0.7,
        amplitude_mod_eps=0.0,
    )

    assert report["status"]["peak_fraction_ok"] is True
    assert report["status"]["integer_close"] is False
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "fail_not_integer_close"


def test_bridge_toyg_c6_mode_index_quantization_negative_control_wrong_operator_sign() -> None:
    report = evaluate_toyg_c6_mode_index_quantization(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        mode_target=1.0,
        tol_mode=0.1,
        min_peak_fraction=0.7,
        amplitude_mod_eps=0.0,
    )

    # Deliberately wrong operator: flip signed mode index.
    wrong_index = -int(report["metrics"]["peak_index_signed"])
    assert abs(wrong_index - 1) >= 2
