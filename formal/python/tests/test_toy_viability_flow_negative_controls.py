from __future__ import annotations

import numpy as np

from formal.python.tools.toy_viability_flow_front_door import SubstrateToyInput, build_toy_viability_report


def _admissible(norm_value: float, *, radius: float) -> bool:
    return float(norm_value) <= float(radius)


def test_toy_viability_flow_negative_control_wrong_sign() -> None:
    radius = 2.0
    etas = [0.0, 0.01, 0.03, 0.05, 0.07]

    correct_pass = 0
    wrong_pass = 0

    for eta in etas:
        inp = SubstrateToyInput(state_dim=2, state_seed=6, eta=eta, grad_kind="identity", grad_params=None)
        report = build_toy_viability_report(inp)

        norm_after = float(report["output"]["norm_after"])
        if _admissible(norm_after, radius=radius):
            correct_pass += 1

        state_before = np.asarray(report["output"]["state_before"], dtype=float)
        wrong_state = state_before + float(eta) * state_before
        wrong_norm = float(np.linalg.norm(wrong_state))
        if _admissible(wrong_norm, radius=radius):
            wrong_pass += 1

    assert correct_pass > 0
    assert wrong_pass < correct_pass


def test_toy_viability_flow_negative_control_parameter_tamper() -> None:
    inp = SubstrateToyInput(state_dim=3, state_seed=4, eta=0.1, grad_kind="identity", grad_params=None)
    report = build_toy_viability_report(inp)

    state_before = np.asarray(report["output"]["state_before"], dtype=float)
    expected = state_before - float(inp.eta) * state_before
    reported = np.asarray(report["output"]["state_after"], dtype=float)

    assert np.allclose(expected, reported)

    tampered_eta = float(inp.eta) + 0.02
    tampered_expected = state_before - tampered_eta * state_before
    assert not np.allclose(tampered_expected, reported)

    tampered_report = build_toy_viability_report(
        SubstrateToyInput(
            state_dim=inp.state_dim,
            state_seed=inp.state_seed,
            eta=tampered_eta,
            grad_kind=inp.grad_kind,
            grad_params=None,
        )
    )

    assert report["input_fingerprint"] != tampered_report["input_fingerprint"]
