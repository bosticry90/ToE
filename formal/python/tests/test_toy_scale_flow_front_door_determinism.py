from __future__ import annotations

from formal.python.tools.toy_scale_flow_front_door import (
    SCHEMA_ID,
    ScaleFlowInput,
    build_toy_scale_flow_report,
)


def test_toy_scale_flow_front_door_is_deterministic() -> None:
    inp = ScaleFlowInput(
        couplings_init=[1.0, -0.5],
        delta=0.1,
        n_steps=3,
        scale_init=0.0,
        candidate_id="E1_euler_linear",
        beta_kind="linear_diag",
        beta_diag=[-0.5, -0.25],
    )

    r1 = build_toy_scale_flow_report(inp)
    r2 = build_toy_scale_flow_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert r1["candidate_id"] == "E1_euler_linear"
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
