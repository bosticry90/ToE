from __future__ import annotations

from formal.python.tools.toy_gauge_redundancy_front_door import (
    GaugeStateInput,
    ToyHInput,
    ToyHParams,
    build_toy_gauge_redundancy_report,
)


def _sum_x(grid: list[list[float]]) -> float:
    return sum(float(x) for x, _ in grid)


def _magnitudes(grid: list[list[float]]) -> list[float]:
    out: list[float] = []
    for x, y in grid:
        out.append((float(x) ** 2 + float(y) ** 2) ** 0.5)
    return out


def test_toy_gauge_redundancy_h2_negative_control_wrong_transform() -> None:
    inp = ToyHInput(
        state=GaugeStateInput(grid=[[1.0, 0.2], [2.0, -0.3], [0.5, 0.4], [0.1, -0.2]]),
        params=ToyHParams(
            dt=0.1,
            steps=2,
            theta=0.2,
            theta_step=0.12,
            epsilon=1e-9,
            gauge_kind="local_phase_rotate",
        ),
        candidate_id="H2_local_phase_gauge",
    )
    report = build_toy_gauge_redundancy_report(inp)

    state_after = [[float(x), float(y)] for x, y in report["output"]["state_after"]]
    wrong_gauge = [[x + 0.25, y] for x, y in state_after]

    mags_after = [float(x) for x in report["output"]["observables"]["magnitudes_after"]]
    mags_wrong = _magnitudes(wrong_gauge)

    assert mags_wrong != mags_after


def test_toy_gauge_redundancy_h2_negative_control_noninvariant_observable() -> None:
    inp = ToyHInput(
        state=GaugeStateInput(grid=[[1.0, 0.2], [2.0, -0.3], [0.5, 0.4], [0.1, -0.2]]),
        params=ToyHParams(
            dt=0.1,
            steps=2,
            theta=0.2,
            theta_step=0.12,
            epsilon=1e-9,
            gauge_kind="local_phase_rotate",
        ),
        candidate_id="H2_local_phase_gauge",
    )
    report = build_toy_gauge_redundancy_report(inp)

    state_after = [[float(x), float(y)] for x, y in report["output"]["state_after"]]
    state_gauge = [[float(x), float(y)] for x, y in report["output"]["state_gauge_after"]]

    sum_after = _sum_x(state_after)
    sum_gauge = _sum_x(state_gauge)

    assert abs(sum_after - sum_gauge) > 1e-6
