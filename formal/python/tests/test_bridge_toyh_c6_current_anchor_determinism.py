from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyh_c6_current_anchor import evaluate_toyh_c6_current_anchor


def test_bridge_toyh_c6_current_anchor_deterministic() -> None:
    report1 = evaluate_toyh_c6_current_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        local_phase_shear_alpha=0.5,
    )
    report2 = evaluate_toyh_c6_current_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        local_phase_shear_alpha=0.5,
    )

    assert report1 == report2
    assert report1["schema_version"] == 1
    assert report1["observable_id"] == "TOYH_C6_current_anchor_proxy_v1"


def test_bridge_toyh_c6_current_anchor_invariant_observables() -> None:
    report = evaluate_toyh_c6_current_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        local_phase_shear_alpha=0.5,
    )
    assert report["status"]["admissible"] is True
    assert report["reason_code"] == "PASS_CURRENT_ANCHOR"


def test_bridge_toyh_c6_current_anchor_resolves_small_alpha_control_case() -> None:
    report = evaluate_toyh_c6_current_anchor(
        theta=float(np.pi / 3.0),
        grid_n=11,
        local_phase_shear_alpha=1e-6,
        tol_current_anchor=1e-7,
        min_anchor_response=1e-8,
    )
    assert report["status"]["admissible"] is True
    assert report["reason_code"] == "PASS_CURRENT_ANCHOR"

