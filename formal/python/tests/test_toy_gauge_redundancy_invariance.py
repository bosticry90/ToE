from __future__ import annotations

from formal.python.tools.toy_gauge_redundancy_front_door import (
    GaugeStateInput,
    ToyHInput,
    ToyHParams,
    build_toy_gauge_redundancy_report,
)


def test_toy_gauge_redundancy_invariance() -> None:
    inp = ToyHInput(
        state=GaugeStateInput(grid=[[1.0, 0.2], [2.0, -0.3], [0.5, 0.4]]),
        params=ToyHParams(dt=0.1, steps=3, theta=0.45, epsilon=1e-9, gauge_kind="phase_rotate"),
        candidate_id="H1_phase_gauge",
    )
    report = build_toy_gauge_redundancy_report(inp)

    observables = report["output"]["observables"]
    deltas = [float(x) for x in observables["delta_magnitudes"]]
    max_delta = float(report["diagnostics"]["max_delta_magnitude"])

    assert max_delta <= float(inp.params.epsilon)
    assert all(d <= float(inp.params.epsilon) for d in deltas)
