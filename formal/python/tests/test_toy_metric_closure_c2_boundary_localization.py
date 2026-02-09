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


def _floor_violations(grid: list[float], *, min_floor: float) -> list[int]:
    return [idx for idx, val in enumerate(grid) if float(val) < float(min_floor)]


def test_toy_metric_closure_c2_boundary_localization() -> None:
    min_floor = 0.5
    max_proxy = 12.0
    params = ToyCParams(scale=1.0, bias=0.0, max_coupling=0.9, min_floor=min_floor, max_proxy=max_proxy)

    good_grid = [1.0, 2.0, 5.0, 10.0, 17.0]
    boundary_grid = [1.0, 2.0, 0.4, 10.0, 17.0]

    good_report = build_toy_metric_closure_report(
        ToyCInput(state=MetricStateInput(grid=good_grid), params=params, candidate_id="C2_curvature_proxy")
    )
    boundary_report = build_toy_metric_closure_report(
        ToyCInput(state=MetricStateInput(grid=boundary_grid), params=params, candidate_id="C2_curvature_proxy")
    )

    assert _admissible_from_report(good_report, min_floor=min_floor, max_proxy=max_proxy)
    assert not _admissible_from_report(boundary_report, min_floor=min_floor, max_proxy=max_proxy)

    violations = _floor_violations(boundary_grid, min_floor=min_floor)
    assert violations == [2]

    assert float(boundary_report["output"]["proxy_abs_max"]) <= max_proxy
