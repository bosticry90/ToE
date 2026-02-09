from __future__ import annotations

from formal.python.tools.toy_gauge_redundancy_front_door import (
    SCHEMA_ID,
    GaugeStateInput,
    ToyHInput,
    ToyHParams,
    build_toy_gauge_redundancy_report,
)


def test_toy_gauge_redundancy_front_door_is_deterministic() -> None:
    inp = ToyHInput(
        state=GaugeStateInput(grid=[[1.0, 0.2], [2.0, -0.3], [0.5, 0.4]]),
        params=ToyHParams(dt=0.1, steps=2, theta=0.3, epsilon=1e-9, gauge_kind="phase_rotate"),
        candidate_id="H1_phase_gauge",
    )

    r1 = build_toy_gauge_redundancy_report(inp)
    r2 = build_toy_gauge_redundancy_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert r1["candidate_id"] == "H1_phase_gauge"
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
