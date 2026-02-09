from __future__ import annotations

from formal.python.tools.toy_viability_flow_front_door import SubstrateToyInput, build_toy_viability_report


def _admissible(norm_value: float, *, radius: float) -> bool:
    return float(norm_value) <= float(radius)


def test_toy_viability_flow_boundary_localization_identity_grad() -> None:
    radius = 2.0
    etas = [0.0, 0.01, 0.03, 0.05, 0.07]

    results: list[bool] = []
    for eta in etas:
        inp = SubstrateToyInput(state_dim=2, state_seed=6, eta=eta, grad_kind="identity", grad_params=None)
        report = build_toy_viability_report(inp)
        norm_after = float(report["output"]["norm_after"])
        results.append(_admissible(norm_after, radius=radius))

    assert any(results)
    assert not all(results)

    transitions = sum(1 for i in range(1, len(results)) if results[i] != results[i - 1])
    assert transitions == 1

    first_true = results.index(True)
    assert all(results[i] for i in range(first_true, len(results)))
    assert all(not results[i] for i in range(0, first_true))
