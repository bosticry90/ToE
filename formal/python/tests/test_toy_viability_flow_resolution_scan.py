from __future__ import annotations

import numpy as np

from formal.python.tools.toy_viability_flow_front_door import (
    SubstrateToyInput,
    apply_viability_step_n,
    build_toy_viability_report,
)


def test_toy_viability_flow_resolution_scan_multistep_converges() -> None:
    eta = 0.4
    base = SubstrateToyInput(state_dim=4, state_seed=12, eta=0.0, grad_kind="identity", grad_params=None)
    report = build_toy_viability_report(base)
    state_before = np.asarray(report["output"]["state_before"], dtype=float)

    s1 = apply_viability_step_n(state=state_before, eta=eta, grad_kind="identity", diag=None, steps=1)
    s2 = apply_viability_step_n(state=state_before, eta=eta, grad_kind="identity", diag=None, steps=2)
    s4 = apply_viability_step_n(state=state_before, eta=eta, grad_kind="identity", diag=None, steps=4)

    d12 = float(np.linalg.norm(s1 - s2))
    d24 = float(np.linalg.norm(s2 - s4))

    assert d24 < d12

    s2_again = apply_viability_step_n(state=state_before, eta=eta, grad_kind="identity", diag=None, steps=2)
    assert np.allclose(s2, s2_again)
