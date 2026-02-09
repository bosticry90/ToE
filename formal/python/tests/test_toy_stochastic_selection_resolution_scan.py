from __future__ import annotations

from formal.python.tools.toy_stochastic_selection_front_door import (
    StochasticSelectionInput,
    build_toy_stochastic_selection_report,
)


def _admissible(initial_state: float, steps: int) -> bool:
    report = build_toy_stochastic_selection_report(
        StochasticSelectionInput(
            seed=122,
            steps=steps,
            dt=0.2,
            initial_state=initial_state,
            pullback_strength=0.5,
            target=0.0,
            sigma=0.3,
            abs_bound=1.0,
            candidate_id="F1_noise_plus_pullback",
        )
    )
    return bool(report["admissibility"]["admissible"])


def test_toy_stochastic_selection_resolution_scan() -> None:
    steps_list = [7, 9, 11]

    pass_results = [_admissible(0.7, steps) for steps in steps_list]
    fail_results = [_admissible(0.8, steps) for steps in steps_list]

    assert all(pass_results)
    assert not any(fail_results)
