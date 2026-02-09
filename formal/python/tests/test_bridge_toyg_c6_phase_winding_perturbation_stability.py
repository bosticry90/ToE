from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_phase_winding import evaluate_toyg_c6_phase_winding


def test_bridge_toyg_c6_phase_winding_perturbation_stability() -> None:
    base = evaluate_toyg_c6_phase_winding(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        winding_target=1.0,
        tol_winding=0.05,
        unwrap_margin=1e-6,
        amplitude_mod_eps=0.0,
    )
    perturbed = evaluate_toyg_c6_phase_winding(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        winding_target=1.0,
        tol_winding=0.05,
        unwrap_margin=1e-6,
        amplitude_mod_eps=1e-4,
    )

    assert base["status"]["admissible"] is True
    assert perturbed["status"]["admissible"] is True
    assert base["metrics"]["nearest_int"] == perturbed["metrics"]["nearest_int"] == 1
    assert abs(float(base["metrics"]["raw_winding"]) - float(perturbed["metrics"]["raw_winding"])) <= 1e-10
