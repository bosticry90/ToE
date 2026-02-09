from __future__ import annotations

from formal.python.tools.toy_coherence_transport_front_door import (
    CoherenceInput,
    SubstrateInput,
    ToyBInput,
    ToyBParams,
    build_toy_coherence_report,
)


def _admissible(coherence_value: float, *, radius: float) -> bool:
    return abs(float(coherence_value)) <= float(radius)


def test_toy_coherence_transport_negative_control_wrong_sign() -> None:
    radius = 2.0
    dts = [0.0, 0.02, 0.03, 0.05, 0.07]

    correct_pass = 0
    wrong_pass = 0

    for dt in dts:
        inp = ToyBInput(
            substrate=SubstrateInput(value=1.0),
            coherence=CoherenceInput(value=2.05),
            params=ToyBParams(dt=dt, alpha=0.0, beta=1.0, source_bias=0.0),
        )
        report = build_toy_coherence_report(inp)
        c_before = float(report["output"]["coherence_before"])
        c_after = float(report["output"]["coherence_after"])

        if _admissible(c_after, radius=radius):
            correct_pass += 1

        wrong_c = c_before + dt * (0.0 + 1.0 * c_before)
        if _admissible(wrong_c, radius=radius):
            wrong_pass += 1

    assert correct_pass > 0
    assert wrong_pass < correct_pass


def test_toy_coherence_transport_negative_control_bad_params() -> None:
    radius = 2.0

    bad_params = ToyBParams(dt=0.1, alpha=10.0, beta=0.0, source_bias=0.0)
    inp = ToyBInput(
        substrate=SubstrateInput(value=1.0),
        coherence=CoherenceInput(value=1.9),
        params=bad_params,
    )

    report = build_toy_coherence_report(inp)
    c_after = float(report["output"]["coherence_after"])

    assert not _admissible(c_after, radius=radius)
