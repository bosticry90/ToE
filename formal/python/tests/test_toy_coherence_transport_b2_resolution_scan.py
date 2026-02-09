from __future__ import annotations

from math import inf

from formal.python.tools.toy_coherence_transport_front_door import (
    CoherenceInput,
    SubstrateInput,
    ToyBInput,
    ToyBParams,
    build_toy_coherence_report,
)


def _admissible_max(grid: list[float], *, radius: float) -> bool:
    return max(abs(x) for x in grid) <= float(radius)


def test_toy_coherence_transport_b2_resolution_scan() -> None:
    radius = 2.0
    c0 = 2.05
    dt_min = 0.0
    dt_max = 0.08

    threshold = 1.0 - (radius / c0)

    for n in [5, 7, 9]:
        step = (dt_max - dt_min) / float(n - 1)
        dts = [dt_min + i * step for i in range(n)]

        results: list[bool] = []
        first_pass_dt = inf

        for dt in dts:
            inp = ToyBInput(
                substrate=SubstrateInput(value=1.0),
                coherence=CoherenceInput(value=c0, grid=[c0] * n),
                params=ToyBParams(dt=dt, alpha=0.0, beta=1.0, source_bias=0.0, transport=0.5),
                candidate_id="B2_transport_proxy",
            )
            report = build_toy_coherence_report(inp)
            grid_after = [float(x) for x in report["output"]["coherence_grid_after"]]
            ok = _admissible_max(grid_after, radius=radius)
            results.append(ok)
            if ok and dt < first_pass_dt:
                first_pass_dt = dt

        transitions = sum(1 for i in range(1, len(results)) if results[i] != results[i - 1])
        assert transitions <= 1

        if any(results):
            assert first_pass_dt >= threshold - 1e-12
            assert first_pass_dt - threshold <= step + 1e-12

        bad_params = ToyBParams(dt=0.1, alpha=10.0, beta=0.0, source_bias=0.0, transport=0.5)
        bad_results: list[bool] = []
        for dt in dts:
            inp = ToyBInput(
                substrate=SubstrateInput(value=1.0),
                coherence=CoherenceInput(value=c0, grid=[c0] * n),
                params=ToyBParams(
                    dt=dt,
                    alpha=bad_params.alpha,
                    beta=bad_params.beta,
                    source_bias=bad_params.source_bias,
                    transport=bad_params.transport,
                ),
                candidate_id="B2_transport_proxy",
            )
            report = build_toy_coherence_report(inp)
            grid_after = [float(x) for x in report["output"]["coherence_grid_after"]]
            bad_results.append(_admissible_max(grid_after, radius=radius))

        assert not any(bad_results)
