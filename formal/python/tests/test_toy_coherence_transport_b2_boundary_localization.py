from __future__ import annotations

from formal.python.tools.toy_coherence_transport_front_door import (
    CoherenceInput,
    SubstrateInput,
    ToyBInput,
    ToyBParams,
    build_toy_coherence_report,
)


def _admissible_max(grid: list[float], *, radius: float) -> bool:
    return max(abs(x) for x in grid) <= float(radius)


def test_toy_coherence_transport_b2_boundary_localization() -> None:
    radius = 2.0
    dts = [0.0, 0.02, 0.03, 0.05, 0.07]

    results: list[bool] = []
    for dt in dts:
        inp = ToyBInput(
            substrate=SubstrateInput(value=1.0),
            coherence=CoherenceInput(value=2.05, grid=[2.05] * 5),
            params=ToyBParams(dt=dt, alpha=0.0, beta=1.0, source_bias=0.0, transport=0.5),
            candidate_id="B2_transport_proxy",
        )
        report = build_toy_coherence_report(inp)
        grid_after = list(report["output"]["coherence_grid_after"])
        results.append(_admissible_max([float(x) for x in grid_after], radius=radius))

    assert any(results)
    assert not all(results)

    transitions = sum(1 for i in range(1, len(results)) if results[i] != results[i - 1])
    assert transitions == 1

    first_true = results.index(True)
    assert all(results[i] for i in range(first_true, len(results)))
    assert all(not results[i] for i in range(0, first_true))
