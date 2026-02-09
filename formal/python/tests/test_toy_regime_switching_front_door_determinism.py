from __future__ import annotations

from formal.python.tools.toy_regime_switching_front_door import (
    SCHEMA_ID,
    RegimeSwitchingInput,
    build_toy_regime_switching_report,
)


def test_toy_regime_switching_front_door_is_deterministic() -> None:
    inp = RegimeSwitchingInput(
        mu_def_id="mu_state",
        mu_c=0.7,
        initial_state=0.2,
        steps=5,
        dt=0.2,
        candidate_id="D1_threshold_switch",
    )

    r1 = build_toy_regime_switching_report(inp)
    r2 = build_toy_regime_switching_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert r1["candidate_id"] == "D1_threshold_switch"
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
