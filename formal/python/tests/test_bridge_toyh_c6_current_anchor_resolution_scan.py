from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyh_c6_current_anchor import evaluate_toyh_c6_current_anchor


def test_bridge_toyh_c6_current_anchor_resolution_scan() -> None:
    for n in [7, 9, 11]:
        report = evaluate_toyh_c6_current_anchor(
            theta=float(np.pi / 3.0),
            grid_n=n,
            local_phase_shear_alpha=1e-6,
            tol_current_anchor=1e-7,
            min_anchor_response=1e-8,
        )
        assert report["status"]["admissible"] is True
        assert report["reason_code"] == "PASS_CURRENT_ANCHOR"

