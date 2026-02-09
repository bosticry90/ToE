from __future__ import annotations

from formal.python.tools.toy_metric_closure_front_door import (
    SCHEMA_ID,
    MetricStateInput,
    ToyCInput,
    ToyCParams,
    build_toy_metric_closure_report,
)


def test_toy_metric_closure_c2_is_deterministic() -> None:
    inp = ToyCInput(
        state=MetricStateInput(grid=[1.0, 2.0, 5.0, 10.0, 17.0]),
        params=ToyCParams(scale=1.0, bias=0.0, max_coupling=0.9, min_floor=0.5, max_proxy=3.0),
        candidate_id="C2_curvature_proxy",
    )

    r1 = build_toy_metric_closure_report(inp)
    r2 = build_toy_metric_closure_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert r1["candidate_id"] == "C2_curvature_proxy"
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
