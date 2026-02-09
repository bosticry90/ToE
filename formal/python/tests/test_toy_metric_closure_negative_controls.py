from __future__ import annotations

from formal.python.tools.toy_metric_closure_front_door import (
    MetricStateInput,
    ToyCInput,
    ToyCParams,
    build_toy_metric_closure_report,
)


def _admissible_from_metric(g_tt: float, g_tx: float, g_xx: float, *, max_coupling: float) -> bool:
    if g_tt >= 0.0 or g_xx <= 0.0:
        return False
    denom = abs(g_tt * g_xx)
    if denom == 0.0:
        return False
    ratio = abs(g_tx) / (denom ** 0.5)
    return ratio <= float(max_coupling)


def test_toy_metric_closure_negative_control_operator_sanity() -> None:
    params = ToyCParams(scale=0.5, bias=0.0, max_coupling=0.9)
    inp = ToyCInput(state=MetricStateInput(grid=[1.0] * 5), params=params)
    report = build_toy_metric_closure_report(inp)

    g_tt = float(report["output"]["g_tt"])
    g_tx = float(report["output"]["g_tx"])
    g_xx = float(report["output"]["g_xx"])

    assert _admissible_from_metric(g_tt, g_tx, g_xx, max_coupling=params.max_coupling)

    wrong_g_tx = g_tx * len(report["output"]["grid"])
    assert not _admissible_from_metric(g_tt, wrong_g_tx, g_xx, max_coupling=params.max_coupling)


def test_toy_metric_closure_negative_control_bad_params() -> None:
    params = ToyCParams(scale=1.5, bias=0.0, max_coupling=0.9)
    inp = ToyCInput(state=MetricStateInput(grid=[1.0] * 5), params=params)
    report = build_toy_metric_closure_report(inp)

    g_tt = float(report["output"]["g_tt"])
    g_tx = float(report["output"]["g_tx"])
    g_xx = float(report["output"]["g_xx"])

    assert not _admissible_from_metric(g_tt, g_tx, g_xx, max_coupling=params.max_coupling)
