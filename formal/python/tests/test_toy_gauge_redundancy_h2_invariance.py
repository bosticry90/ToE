from __future__ import annotations

from formal.python.tools.toy_gauge_redundancy_front_door import (
    GaugeStateInput,
    ToyHInput,
    ToyHParams,
    build_toy_gauge_redundancy_report,
)


def test_toy_gauge_redundancy_h2_invariance_local_gauge() -> None:
    inp = ToyHInput(
        state=GaugeStateInput(grid=[[1.0, 0.2], [2.0, -0.3], [0.5, 0.4], [0.1, -0.2]]),
        params=ToyHParams(
            dt=0.1,
            steps=3,
            theta=0.4,
            theta_step=0.21,
            epsilon=1e-9,
            gauge_kind="local_phase_rotate",
        ),
        candidate_id="H2_local_phase_gauge",
    )
    report = build_toy_gauge_redundancy_report(inp)

    max_delta = float(report["diagnostics"]["max_delta_magnitude"])
    assert max_delta <= float(inp.params.epsilon)
