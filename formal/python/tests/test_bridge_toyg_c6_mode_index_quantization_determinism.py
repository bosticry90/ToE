from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyg_c6_mode_index_quantization import (
    evaluate_toyg_c6_mode_index_quantization,
)


def test_bridge_toyg_c6_mode_index_quantization_deterministic() -> None:
    report1 = evaluate_toyg_c6_mode_index_quantization(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        mode_target=1.0,
        tol_mode=0.1,
        min_peak_fraction=0.7,
        amplitude_mod_eps=0.0,
    )
    report2 = evaluate_toyg_c6_mode_index_quantization(
        grid_n=11,
        loop_length=float(2.0 * np.pi),
        mode_target=1.0,
        tol_mode=0.1,
        min_peak_fraction=0.7,
        amplitude_mod_eps=0.0,
    )

    assert report1 == report2
    assert report1["schema_version"] == 1
    assert report1["observable_id"] == "TOYG_C6_mode_index_quantization_v1"
    assert report1["status"]["admissible"] is True
    assert report1["reason_code"] == "pass_mode_index_1"
