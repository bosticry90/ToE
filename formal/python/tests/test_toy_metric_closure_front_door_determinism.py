from __future__ import annotations

from formal.python.tools.toy_metric_closure_front_door import (
    SCHEMA_ID,
    MetricStateInput,
    ToyCInput,
    ToyCParams,
    build_toy_metric_closure_report,
)


def test_toy_metric_closure_front_door_is_deterministic() -> None:
    inp = ToyCInput(
        state=MetricStateInput(grid=[1.0, 1.0, 1.0]),
        params=ToyCParams(scale=0.85, bias=0.0, max_coupling=0.9),
    )

    r1 = build_toy_metric_closure_report(inp)
    r2 = build_toy_metric_closure_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert r1["candidate_id"] == "C1_signature"
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
