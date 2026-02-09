from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_phase_winding import evaluate_toyg_c6_phase_winding


def test_bridge_toyg_c6_phase_winding_deterministic() -> None:
    report1 = evaluate_toyg_c6_phase_winding(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        winding_target=1.0,
        tol_winding=0.05,
        unwrap_margin=1e-6,
        amplitude_mod_eps=0.0,
    )
    report2 = evaluate_toyg_c6_phase_winding(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        winding_target=1.0,
        tol_winding=0.05,
        unwrap_margin=1e-6,
        amplitude_mod_eps=0.0,
    )

    assert report1 == report2
    assert report1["schema_version"] == 1
    assert report1["observable_id"] == "TOYG_C6_phase_winding_quantization_v1"
    assert report1["status"]["admissible"] is True
    assert report1["reason_code"] == "pass_quantized_winding_1"
