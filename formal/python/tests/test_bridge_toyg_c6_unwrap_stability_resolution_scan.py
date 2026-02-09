from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_unwrap_stability import evaluate_toyg_c6_unwrap_stability


def test_bridge_toyg_c6_unwrap_stability_resolution_scan() -> None:
    loop_length = float(2.0 * np.pi)
    tol_step_mean = 0.05
    tol_step_std = 0.05
    min_near_pi_fraction = 0.8
    pi_edge_eps = 0.15

    for n in [7, 9, 11]:
        admissible = evaluate_toyg_c6_unwrap_stability(
            grid_n=n,
            loop_length=loop_length,
            unwrap_target=0.5 * n,
            tol_step_mean=tol_step_mean,
            tol_step_std=tol_step_std,
            min_near_pi_fraction=min_near_pi_fraction,
            pi_edge_eps=pi_edge_eps,
            amplitude_mod_eps=0.0,
            phase_shear_eps=0.0,
        )
        inadmissible = evaluate_toyg_c6_unwrap_stability(
            grid_n=n,
            loop_length=loop_length,
            unwrap_target=0.5 * n - 0.5,
            tol_step_mean=tol_step_mean,
            tol_step_std=tol_step_std,
            min_near_pi_fraction=min_near_pi_fraction,
            pi_edge_eps=pi_edge_eps,
            amplitude_mod_eps=0.0,
            phase_shear_eps=0.0,
        )

        assert admissible["status"]["admissible"] is True
        assert admissible["reason_code"] == "pass_unwrap_stable_boundary"
        assert inadmissible["status"]["admissible"] is False
        assert inadmissible["reason_code"] == "fail_not_boundary_sensitive"
