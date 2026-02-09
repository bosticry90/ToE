from __future__ import annotations

from formal.python.tools.toy_coherence_transport_front_door import (
    CoherenceInput,
    SubstrateInput,
    ToyBInput,
    ToyBParams,
    build_toy_coherence_report,
)


def _admissible_max(grid: list[float], *, radius: float) -> bool:
    return max(abs(x) for x in grid) <= float(radius)


def _transport_step(
    grid: list[float], *, substrate: float, params: ToyBParams, flip_direction: bool
) -> list[float]:
    u = float(params.transport) * float(substrate)
    if flip_direction:
        u = -u

    source = float(params.alpha) * float(substrate) + float(params.source_bias)
    beta = float(params.beta)
    dt = float(params.dt)

    n = len(grid)
    next_grid: list[float] = []
    for i in range(n):
        prev_val = float(grid[i - 1])
        cur_val = float(grid[i])
        term = u * (prev_val - cur_val)
        next_grid.append(cur_val + dt * (term + source - beta * cur_val))
    return next_grid


def test_toy_coherence_transport_b2_negative_control_wrong_sign() -> None:
    radius = 2.03
    grid = [2.05, 1.0, 1.0, 1.0, 1.0]
    params = ToyBParams(dt=0.05, alpha=0.0, beta=0.0, source_bias=0.0, transport=0.5)

    inp = ToyBInput(
        substrate=SubstrateInput(value=1.0),
        coherence=CoherenceInput(value=2.05, grid=list(grid)),
        params=params,
        candidate_id="B2_transport_proxy",
    )
    report = build_toy_coherence_report(inp)
    correct_after = [float(x) for x in report["output"]["coherence_grid_after"]]

    wrong_after = _transport_step(grid, substrate=1.0, params=params, flip_direction=True)

    assert _admissible_max(correct_after, radius=radius)
    assert not _admissible_max(wrong_after, radius=radius)


def test_toy_coherence_transport_b2_negative_control_bad_params() -> None:
    radius = 2.0
    params = ToyBParams(dt=0.1, alpha=10.0, beta=0.0, source_bias=0.0, transport=0.5)

    inp = ToyBInput(
        substrate=SubstrateInput(value=1.0),
        coherence=CoherenceInput(value=1.9, grid=[1.9] * 5),
        params=params,
        candidate_id="B2_transport_proxy",
    )

    report = build_toy_coherence_report(inp)
    grid_after = [float(x) for x in report["output"]["coherence_grid_after"]]

    assert not _admissible_max(grid_after, radius=radius)
