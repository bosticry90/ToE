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


def test_toy_coherence_transport_boundary_localization() -> None:
    radius = 2.0
    dts = [0.0, 0.02, 0.03, 0.05, 0.07]

    results: list[bool] = []
    for dt in dts:
        inp = ToyBInput(
            substrate=SubstrateInput(value=1.0),
            coherence=CoherenceInput(value=2.05),
            params=ToyBParams(dt=dt, alpha=0.0, beta=1.0, source_bias=0.0),
        )
        report = build_toy_coherence_report(inp)
        c_after = float(report["output"]["coherence_after"])
        results.append(_admissible(c_after, radius=radius))

    assert any(results)
    assert not all(results)

    transitions = sum(1 for i in range(1, len(results)) if results[i] != results[i - 1])
    assert transitions == 1

    first_true = results.index(True)
    assert all(results[i] for i in range(first_true, len(results)))
    assert all(not results[i] for i in range(0, first_true))
