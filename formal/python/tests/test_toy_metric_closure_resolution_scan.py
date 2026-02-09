from __future__ import annotations

from math import inf

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


def test_toy_metric_closure_resolution_scan() -> None:
    max_coupling = 0.9
    scale = 0.85

    for n in [5, 7, 9]:
        inp = ToyCInput(
            state=MetricStateInput(grid=[1.0] * n),
            params=ToyCParams(scale=scale, bias=0.0, max_coupling=max_coupling),
        )
        report = build_toy_metric_closure_report(inp)
        assert _admissible_from_report(report, max_coupling=max_coupling)

        bad_params = ToyCParams(scale=1.2, bias=0.0, max_coupling=max_coupling)
        bad_report = build_toy_metric_closure_report(
            ToyCInput(state=MetricStateInput(grid=[1.0] * n), params=bad_params)
        )
        assert not _admissible_from_report(bad_report, max_coupling=max_coupling)

    thresholds: list[float] = []
    for n in [5, 7, 9]:
        step = 0.04
        scales = [0.8 + i * step for i in range(6)]
        first_pass = inf
        for s in scales:
            inp = ToyCInput(
                state=MetricStateInput(grid=[1.0] * n),
                params=ToyCParams(scale=s, bias=0.0, max_coupling=max_coupling),
            )
            report = build_toy_metric_closure_report(inp)
            if _admissible_from_report(report, max_coupling=max_coupling) and s < first_pass:
                first_pass = s
        thresholds.append(first_pass)

    assert max(thresholds) - min(thresholds) <= 0.04
