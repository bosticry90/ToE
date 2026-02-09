from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_mode_index_quantization import (
    evaluate_toyg_c6_mode_index_quantization,
)


def test_bridge_toyg_c6_mode_index_quantization_perturbation_stability() -> None:
    base = evaluate_toyg_c6_mode_index_quantization(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        mode_target=1.0,
        tol_mode=0.1,
        min_peak_fraction=0.7,
        amplitude_mod_eps=0.0,
    )
    perturbed = evaluate_toyg_c6_mode_index_quantization(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        mode_target=1.0,
        tol_mode=0.1,
        min_peak_fraction=0.7,
        amplitude_mod_eps=1e-4,
    )

    assert base["status"]["admissible"] is True
    assert perturbed["status"]["admissible"] is True
    assert base["metrics"]["peak_index_signed"] == perturbed["metrics"]["peak_index_signed"] == 1
    assert float(base["metrics"]["peak_fraction"]) >= 0.99
    assert float(perturbed["metrics"]["peak_fraction"]) >= 0.99
