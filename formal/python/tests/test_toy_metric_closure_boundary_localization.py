from __future__ import annotations

from formal.python.tools.toy_metric_closure_front_door import (
    MetricStateInput,
    ToyCInput,
    ToyCParams,
    build_toy_metric_closure_report,
)


def _admissible_from_report(report: dict, *, max_coupling: float) -> bool:
    g_tt = float(report["output"]["g_tt"])
    g_tx = float(report["output"]["g_tx"])
    g_xx = float(report["output"]["g_xx"])
    if g_tt >= 0.0 or g_xx <= 0.0:
        return False
    denom = abs(g_tt * g_xx)
    if denom == 0.0:
        return False
    ratio = abs(g_tx) / (denom ** 0.5)
    return ratio <= float(max_coupling)


def test_toy_metric_closure_boundary_localization() -> None:
    max_coupling = 0.9
    scales = [0.8, 0.85, 0.9, 0.95, 1.0]

    results: list[bool] = []
    for scale in scales:
        inp = ToyCInput(
            state=MetricStateInput(grid=[1.0, 1.0, 1.0, 1.0, 1.0]),
            params=ToyCParams(scale=scale, bias=0.0, max_coupling=max_coupling),
        )
        report = build_toy_metric_closure_report(inp)
        results.append(_admissible_from_report(report, max_coupling=max_coupling))

    assert any(results)
    assert not all(results)

    transitions = sum(1 for i in range(1, len(results)) if results[i] != results[i - 1])
    assert transitions == 1

    nondecreasing = all(results[i] <= results[i + 1] for i in range(len(results) - 1))
    nonincreasing = all(results[i] >= results[i + 1] for i in range(len(results) - 1))
    assert nondecreasing or nonincreasing
