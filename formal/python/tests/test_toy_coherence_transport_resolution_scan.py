from __future__ import annotations

from math import inf

from formal.python.tools.toy_coherence_transport_front_door import (
    CoherenceInput,
    SubstrateInput,
    ToyBInput,
    ToyBParams,
    build_toy_coherence_report,
)


def _admissible(coherence_value: float, *, radius: float) -> bool:
    return abs(float(coherence_value)) <= float(radius)


def test_toy_coherence_transport_resolution_scan() -> None:
    radius = 2.0
    c0 = 2.05
    dt_min = 0.0
    dt_max = 0.08

    threshold = 1.0 - (radius / c0)

    for n in [5, 7, 9]:
        step = (dt_max - dt_min) / float(n - 1)
        dts = [dt_min + i * step for i in range(n)]

        results: list[bool] = []
        wrong_results: list[bool] = []
        first_pass_dt = inf

        for dt in dts:
            inp = ToyBInput(
                substrate=SubstrateInput(value=1.0),
                coherence=CoherenceInput(value=c0),
                params=ToyBParams(dt=dt, alpha=0.0, beta=1.0, source_bias=0.0),
            )
            report = build_toy_coherence_report(inp)
            c_before = float(report["output"]["coherence_before"])
            c_after = float(report["output"]["coherence_after"])

            ok = _admissible(c_after, radius=radius)
            results.append(ok)
            if ok and dt < first_pass_dt:
                first_pass_dt = dt

            wrong_c = c_before + dt * (0.0 + 1.0 * c_before)
            wrong_results.append(_admissible(wrong_c, radius=radius))

        transitions = sum(1 for i in range(1, len(results)) if results[i] != results[i - 1])
        assert transitions <= 1

        if any(results):
            assert first_pass_dt >= threshold - 1e-12
            assert first_pass_dt - threshold <= step + 1e-12

        assert not any(wrong_results)
