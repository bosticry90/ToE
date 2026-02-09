from __future__ import annotations

from formal.python.tools.toy_stochastic_selection_front_door import (
    StochasticSelectionInput,
    build_toy_stochastic_selection_report,
)


def test_toy_stochastic_selection_boundary_localization() -> None:
    base_kwargs = dict(
        seed=122,
        steps=2,
        dt=0.2,
        pullback_strength=0.5,
        target=0.0,
        sigma=0.3,
        abs_bound=1.0,
        candidate_id="F1_noise_plus_pullback",
    )

    pass_case = build_toy_stochastic_selection_report(
        StochasticSelectionInput(initial_state=0.75, **base_kwargs)
    )
    assert pass_case["admissibility"]["admissible"] is True
    assert pass_case["admissibility"]["violations"] == []

    fail_case = build_toy_stochastic_selection_report(
        StochasticSelectionInput(initial_state=0.8, **base_kwargs)
    )
    assert fail_case["admissibility"]["admissible"] is False
    assert fail_case["diagnostics"]["reason_code"] == "BOUND_EXCEEDED"

    violations = list(fail_case["admissibility"]["violations"])
    assert len(violations) == 1
    v0 = violations[0]
    assert v0["step"] == 1

    admissible_sequence = list(fail_case["output"]["admissible_sequence"])
    assert admissible_sequence[0] is True
    assert admissible_sequence[1] is False
