from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_unwrap_stability import evaluate_toyg_c6_unwrap_stability


def test_bridge_toyg_c6_unwrap_stability_perturbation_stability() -> None:
    base = evaluate_toyg_c6_unwrap_stability(
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
    perturbed = evaluate_toyg_c6_unwrap_stability(
        grid_n=7,
        loop_length=float(2.0 * np.pi),
        unwrap_target=3.5,
        tol_step_mean=0.05,
        tol_step_std=0.05,
        min_near_pi_fraction=0.8,
        pi_edge_eps=0.15,
        amplitude_mod_eps=1e-4,
        phase_shear_eps=0.0,
    )

    assert base["status"]["admissible"] is True
    assert perturbed["status"]["admissible"] is True
    assert float(base["metrics"]["near_pi_fraction"]) >= 0.99
    assert float(perturbed["metrics"]["near_pi_fraction"]) >= 0.99
