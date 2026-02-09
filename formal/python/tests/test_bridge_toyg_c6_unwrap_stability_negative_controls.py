from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_unwrap_stability import evaluate_toyg_c6_unwrap_stability


def test_bridge_toyg_c6_unwrap_stability_negative_control_not_boundary_sensitive() -> None:
    report = evaluate_toyg_c6_unwrap_stability(
        grid_n=7,
        loop_length=float(2.0 * np.pi),
        unwrap_target=3.0,
        tol_step_mean=0.05,
        tol_step_std=0.05,
        min_near_pi_fraction=0.8,
        pi_edge_eps=0.15,
        amplitude_mod_eps=0.0,
        phase_shear_eps=0.0,
    )

    assert report["status"]["near_pi_sensitive"] is False
    assert report["status"]["admissible"] is False
    assert report["reason_code"] == "fail_not_boundary_sensitive"


def test_bridge_toyg_c6_unwrap_stability_negative_control_wrong_operator_sign() -> None:
    report = evaluate_toyg_c6_unwrap_stability(
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

    # Deliberately wrong operator: invert the near-pi fraction decision.
    wrong_near_pi_fraction = 1.0 - float(report["metrics"]["near_pi_fraction"])
    assert wrong_near_pi_fraction < float(report["inputs"]["min_near_pi_fraction"])
