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


def _grid_quadratic(n: int) -> list[float]:
    return [float(i * i + 1) for i in range(n)]


def test_toy_metric_closure_c2_resolution_scan() -> None:
    min_floor = 0.5
    max_proxy = 12.0

    for n in [5, 7, 9]:
        good_grid = _grid_quadratic(n)
        good_report = build_toy_metric_closure_report(
            ToyCInput(
                state=MetricStateInput(grid=good_grid),
                params=ToyCParams(scale=0.9, bias=0.0, max_coupling=0.9, min_floor=min_floor, max_proxy=max_proxy),
                candidate_id="C2_curvature_proxy",
            )
        )
        assert _admissible_from_report(good_report, min_floor=min_floor, max_proxy=max_proxy)

        bad_grid = list(good_grid)
        mid = n // 2
        bad_grid[mid] = 0.4
        bad_report = build_toy_metric_closure_report(
            ToyCInput(
                state=MetricStateInput(grid=bad_grid),
                params=ToyCParams(scale=0.9, bias=0.0, max_coupling=0.9, min_floor=min_floor, max_proxy=max_proxy),
                candidate_id="C2_curvature_proxy",
            )
        )
        assert not _admissible_from_report(bad_report, min_floor=min_floor, max_proxy=max_proxy)
