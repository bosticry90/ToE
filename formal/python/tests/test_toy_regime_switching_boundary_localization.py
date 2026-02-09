from __future__ import annotations

from formal.python.tools.toy_regime_switching_front_door import RegimeSwitchingInput, build_toy_regime_switching_report


def _admissible_exactly_one_flip(report: dict) -> bool:
    return int(report["output"]["summary"]["flip_count"]) == 1


def test_toy_regime_switching_boundary_localization() -> None:
    mu_cs = [0.6, 0.7, 0.8, 0.9, 1.0]
    results: list[bool] = []
    for mu_c in mu_cs:
        inp = RegimeSwitchingInput(
            mu_def_id="mu_state",
            mu_c=mu_c,
            initial_state=0.2,
            steps=5,
            dt=0.2,
            candidate_id="D1_threshold_switch",
        )
        report = build_toy_regime_switching_report(inp)
        results.append(_admissible_exactly_one_flip(report))

    assert any(results)
    assert not all(results)

    transitions = sum(1 for i in range(1, len(results)) if results[i] != results[i - 1])
    assert transitions == 1

    nonincreasing = all(results[i] >= results[i + 1] for i in range(len(results) - 1))
    assert nonincreasing
