from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_phase_winding import evaluate_toyg_c6_phase_winding


def test_bridge_toyg_c6_phase_winding_resolution_scan() -> None:
    loop_length = float(2.0 * np.pi)
    tol_winding = 0.05
    unwrap_margin = 1e-6

    for n in [7, 9, 11]:
        admissible = evaluate_toyg_c6_phase_winding(
            grid_n=n,
            loop_length=loop_length,
            winding_target=1.0,
            tol_winding=tol_winding,
            unwrap_margin=unwrap_margin,
            amplitude_mod_eps=0.0,
        )
        inadmissible = evaluate_toyg_c6_phase_winding(
            grid_n=n,
            loop_length=loop_length,
            winding_target=1.25,
            tol_winding=tol_winding,
            unwrap_margin=unwrap_margin,
            amplitude_mod_eps=0.0,
        )

        assert admissible["status"]["admissible"] is True
        assert admissible["metrics"]["nearest_int"] == 1
        assert inadmissible["status"]["admissible"] is False
        assert inadmissible["reason_code"] == "fail_not_integer_close"
