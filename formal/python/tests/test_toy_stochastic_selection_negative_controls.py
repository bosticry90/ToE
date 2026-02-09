from __future__ import annotations

import hashlib

from formal.python.tools.toy_stochastic_selection_front_door import (
    StochasticSelectionInput,
    build_toy_stochastic_selection_report,
)


def _q(x: float, *, sig: int = 12) -> float:
    return float(f"{float(x):.{int(sig)}g}")


def _noise_value(seed: int, step: int) -> float:
    text = f"{int(seed)}:{int(step)}"
    digest = hashlib.sha256(text.encode("utf-8")).digest()
    u = int.from_bytes(digest[:8], "big") / float(2**64)
    return 2.0 * u - 1.0


def _wrong_state_sequence(*, seed: int, steps: int, state: float, sigma: float) -> list[float]:
    seq = [float(state)]
    current = float(state)
    for step in range(int(steps)):
        current = float(current) + float(sigma) * float(_noise_value(seed, step))
        seq.append(current)
    return seq


def _expected_pullback_sequence(*, state: float, steps: int, dt: float, k: float, target: float) -> list[float]:
    seq = [float(state)]
    current = float(state)
    for _ in range(int(steps)):
        current = float(current) + float(dt) * float(k) * (float(target) - float(current))
        seq.append(current)
    return seq


def test_toy_stochastic_selection_negative_control_operator_sanity() -> None:
    inp = StochasticSelectionInput(
        seed=122,
        steps=2,
        dt=0.2,
        initial_state=0.75,
        pullback_strength=0.5,
        target=0.0,
        sigma=0.3,
        abs_bound=1.0,
        candidate_id="F1_noise_plus_pullback",
    )
    report = build_toy_stochastic_selection_report(inp)
    assert report["admissibility"]["admissible"] is True

    wrong_seq = _wrong_state_sequence(
        seed=inp.seed,
        steps=inp.steps,
        state=inp.initial_state,
        sigma=inp.sigma,
    )
    wrong_violation = any(abs(float(x)) > float(inp.abs_bound) for x in wrong_seq)
    assert wrong_violation is True


def test_toy_stochastic_selection_negative_control_noise_disabled() -> None:
    inp = StochasticSelectionInput(
        seed=7,
        steps=3,
        dt=0.2,
        initial_state=0.5,
        pullback_strength=0.5,
        target=1.0,
        sigma=0.0,
        abs_bound=2.0,
        candidate_id="F1_noise_plus_pullback",
    )
    report = build_toy_stochastic_selection_report(inp)
    expected = _expected_pullback_sequence(
        state=inp.initial_state,
        steps=inp.steps,
        dt=inp.dt,
        k=inp.pullback_strength,
        target=inp.target,
    )

    expected_q = [_q(x) for x in expected]
    actual = list(report["output"]["state_sequence"])
    assert actual == expected_q
