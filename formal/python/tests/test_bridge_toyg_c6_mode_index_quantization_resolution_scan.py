from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_mode_index_quantization import (
    evaluate_toyg_c6_mode_index_quantization,
)


def test_bridge_toyg_c6_mode_index_quantization_resolution_scan() -> None:
    loop_length = float(2.0 * np.pi)
    tol_mode = 0.1
    min_peak_fraction = 0.7

    for n in [7, 9, 11]:
        admissible = evaluate_toyg_c6_mode_index_quantization(
            grid_n=n,
            loop_length=loop_length,
            mode_target=1.0,
            tol_mode=tol_mode,
            min_peak_fraction=min_peak_fraction,
            amplitude_mod_eps=0.0,
        )
        inadmissible = evaluate_toyg_c6_mode_index_quantization(
            grid_n=n,
            loop_length=loop_length,
            mode_target=1.25,
            tol_mode=tol_mode,
            min_peak_fraction=min_peak_fraction,
            amplitude_mod_eps=0.0,
        )

        assert admissible["status"]["admissible"] is True
        assert admissible["metrics"]["peak_index_signed"] == 1
        assert inadmissible["status"]["admissible"] is False
        assert inadmissible["reason_code"] == "fail_not_integer_close"
