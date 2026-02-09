from __future__ import annotations

from formal.python.tools.toy_stochastic_selection_front_door import (
    SCHEMA_ID,
    StochasticSelectionInput,
    build_toy_stochastic_selection_report,
)


def test_toy_stochastic_selection_front_door_is_deterministic() -> None:
    inp = StochasticSelectionInput(
        seed=7,
        steps=3,
        dt=0.2,
        initial_state=0.4,
        pullback_strength=0.5,
        target=0.0,
        sigma=0.3,
        abs_bound=1.0,
        candidate_id="F1_noise_plus_pullback",
    )

    r1 = build_toy_stochastic_selection_report(inp)
    r2 = build_toy_stochastic_selection_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert r1["candidate_id"] == "F1_noise_plus_pullback"
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
