from __future__ import annotations

from formal.python.tools.toy_regime_switching_front_door import RegimeSwitchingInput, build_toy_regime_switching_report


def _flip_count(report: dict) -> int:
    return int(report["output"]["summary"]["flip_count"])


def test_toy_regime_switching_resolution_scan() -> None:
    for steps in [5, 7, 9]:
        good = build_toy_regime_switching_report(
            RegimeSwitchingInput(
                mu_def_id="mu_state",
                mu_c=0.7,
                initial_state=0.2,
                steps=steps,
                dt=0.2,
                candidate_id="D1_threshold_switch",
            )
        )
        assert _flip_count(good) == 1

        bad = build_toy_regime_switching_report(
            RegimeSwitchingInput(
                mu_def_id="mu_state",
                mu_c=0.95,
                initial_state=0.2,
                steps=steps,
                dt=0.2,
                candidate_id="D1_threshold_switch",
            )
        )
        assert _flip_count(bad) == 0
