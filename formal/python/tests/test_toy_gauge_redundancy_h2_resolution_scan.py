from __future__ import annotations

from formal.python.tools.toy_gauge_redundancy_front_door import (
    GaugeStateInput,
    ToyHInput,
    ToyHParams,
    build_toy_gauge_redundancy_report,
)


def test_toy_gauge_redundancy_h2_resolution_scan() -> None:
    sizes = [5, 7, 9]
    results = []
    for n in sizes:
        grid = [[float(i + 1), -0.5 * float(i + 1)] for i in range(n)]
        report = build_toy_gauge_redundancy_report(
            ToyHInput(
                state=GaugeStateInput(grid=grid),
                params=ToyHParams(
                    dt=0.05,
                    steps=3,
                    theta=0.25,
                    theta_step=0.11,
                    epsilon=1e-9,
                    gauge_kind="local_phase_rotate",
                ),
                candidate_id="H2_local_phase_gauge",
            )
        )
        max_delta = float(report["diagnostics"]["max_delta_magnitude"])
        results.append(max_delta <= 1e-9)

    assert all(results)
