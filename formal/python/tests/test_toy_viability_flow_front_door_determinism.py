from __future__ import annotations

from formal.python.tools.toy_viability_flow_front_door import (
    SCHEMA_ID,
    SubstrateToyInput,
    build_toy_viability_report,
)


def test_toy_viability_flow_front_door_is_deterministic() -> None:
    inp = SubstrateToyInput(state_dim=4, state_seed=7, eta=0.1, grad_kind="identity", grad_params=None)

    r1 = build_toy_viability_report(inp)
    r2 = build_toy_viability_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
