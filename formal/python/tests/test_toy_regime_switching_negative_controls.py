from __future__ import annotations

from formal.python.tools.toy_regime_switching_front_door import RegimeSwitchingInput, build_toy_regime_switching_report


def _invert_regime(mu: float, mu_c: float) -> str:
    return "coherent" if mu <= mu_c else "incoherent"


def test_toy_regime_switching_negative_control_inverted_selector() -> None:
    inp = RegimeSwitchingInput(
        mu_def_id="mu_state",
        mu_c=0.7,
        initial_state=0.2,
        steps=5,
        dt=0.2,
        candidate_id="D1_threshold_switch",
    )
    report = build_toy_regime_switching_report(inp)

    mu_seq = [float(x) for x in report["output"]["mu_sequence"]]
    inverted = [_invert_regime(mu, inp.mu_c) for mu in mu_seq]

    assert inverted != report["output"]["regime_sequence"]
    assert inverted[0] != report["output"]["regime_sequence"][0]


def test_toy_regime_switching_negative_control_bad_params_no_switch() -> None:
    inp = RegimeSwitchingInput(
        mu_def_id="mu_state",
        mu_c=0.95,
        initial_state=0.2,
        steps=5,
        dt=0.2,
        candidate_id="D1_threshold_switch",
    )
    report = build_toy_regime_switching_report(inp)
    assert int(report["output"]["summary"]["flip_count"]) == 0
