from __future__ import annotations

import numpy as np

from formal.python.tools.bridge_toyh_c6_phase_anchor import evaluate_toyh_c6_phase_anchor


def test_bridge_toyh_c6_phase_anchor_deterministic() -> None:
    report1 = evaluate_toyh_c6_phase_anchor(theta=float(np.pi / 3.0), grid_n=11)
    report2 = evaluate_toyh_c6_phase_anchor(theta=float(np.pi / 3.0), grid_n=11)

    assert report1 == report2
    assert report1["schema_version"] == 1
    assert report1["observable_id"] == "TOYH_C6_phase_anchor_proxy_v1"


def test_bridge_toyh_c6_phase_anchor_invariant_observables() -> None:
    report = evaluate_toyh_c6_phase_anchor(theta=float(np.pi / 3.0), grid_n=11)
    assert report["status"]["admissible"] is True
    assert report["reason_code"] == "PASS_PHASE_ANCHOR"


def test_bridge_toyh_c6_phase_anchor_resolves_small_theta_control_case() -> None:
    report = evaluate_toyh_c6_phase_anchor(
        theta=1e-6,
        grid_n=11,
        tol_phase_anchor=1e-7,
    )
    assert report["status"]["admissible"] is True
    assert report["reason_code"] == "PASS_PHASE_ANCHOR"

