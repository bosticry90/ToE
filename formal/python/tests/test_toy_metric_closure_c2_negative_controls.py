from __future__ import annotations

from formal.python.tools.toy_metric_closure_front_door import (
    MetricStateInput,
    ToyCInput,
    ToyCParams,
    build_toy_metric_closure_report,
)


def _admissible_from_report(report: dict, *, min_floor: float, max_proxy: float) -> bool:
    proxy_mean = float(report["output"]["proxy_mean"])
    proxy_abs_max = float(report["output"]["proxy_abs_max"])
    min_value = float(report["output"]["min_value"])
    if min_value < float(min_floor):
        return False
    if proxy_abs_max > float(max_proxy):
        return False
    if proxy_mean < 0.0:
        return False
    return True


def test_toy_metric_closure_c2_negative_control_operator_sanity() -> None:
    params = ToyCParams(scale=1.0, bias=0.0, max_coupling=0.9, min_floor=0.5, max_proxy=12.0)
    inp = ToyCInput(
        state=MetricStateInput(grid=[1.0, 2.0, 5.0, 10.0, 17.0]),
        params=params,
        candidate_id="C2_curvature_proxy",
    )
    report = build_toy_metric_closure_report(inp)
    assert _admissible_from_report(report, min_floor=params.min_floor, max_proxy=params.max_proxy)

    wrong_report = dict(report)
    wrong_report["output"] = dict(report["output"])
    wrong_report["output"]["proxy_mean"] = -float(report["output"]["proxy_mean"])
    assert not _admissible_from_report(wrong_report, min_floor=params.min_floor, max_proxy=params.max_proxy)


def test_toy_metric_closure_c2_negative_control_bad_params() -> None:
    params = ToyCParams(scale=1.0, bias=0.0, max_coupling=0.9, min_floor=0.5, max_proxy=1.0)
    inp = ToyCInput(
        state=MetricStateInput(grid=[1.0, 2.0, 5.0, 10.0, 17.0]),
        params=params,
        candidate_id="C2_curvature_proxy",
    )
    report = build_toy_metric_closure_report(inp)
    assert not _admissible_from_report(report, min_floor=params.min_floor, max_proxy=params.max_proxy)


def test_toy_metric_closure_c2_negative_control_bad_state_floor() -> None:
    params = ToyCParams(scale=1.0, bias=0.0, max_coupling=0.9, min_floor=0.5, max_proxy=12.0)
    bad_grid = [1.0, 2.0, 0.4, 10.0, 17.0]
    report = build_toy_metric_closure_report(
        ToyCInput(state=MetricStateInput(grid=bad_grid), params=params, candidate_id="C2_curvature_proxy")
    )

    assert not _admissible_from_report(report, min_floor=params.min_floor, max_proxy=params.max_proxy)
