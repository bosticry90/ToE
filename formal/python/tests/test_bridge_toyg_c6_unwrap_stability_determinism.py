from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_unwrap_stability import evaluate_toyg_c6_unwrap_stability


def test_bridge_toyg_c6_unwrap_stability_deterministic() -> None:
    report1 = evaluate_toyg_c6_unwrap_stability(
        grid_n=7,
        loop_length=float(2.0 * np.pi),
        unwrap_target=3.5,
        tol_step_mean=0.05,
        tol_step_std=0.05,
        min_near_pi_fraction=0.8,
        pi_edge_eps=0.15,
        amplitude_mod_eps=0.0,
        phase_shear_eps=0.0,
    )
    report2 = evaluate_toyg_c6_unwrap_stability(
        grid_n=7,
        loop_length=float(2.0 * np.pi),
        unwrap_target=3.5,
        tol_step_mean=0.05,
        tol_step_std=0.05,
        min_near_pi_fraction=0.8,
        pi_edge_eps=0.15,
        amplitude_mod_eps=0.0,
        phase_shear_eps=0.0,
    )

    assert report1 == report2
    assert report1["schema_version"] == 1
    assert report1["observable_id"] == "TOYG_C6_unwrap_stability_proxy_v1"
    assert report1["status"]["admissible"] is True
    assert report1["reason_code"] == "pass_unwrap_stable_boundary"
