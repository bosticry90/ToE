from __future__ import annotations

from math import sqrt

from formal.python.tools.toy_scale_flow_front_door import ScaleFlowInput, build_toy_scale_flow_report


def _step_euler(g: list[float], delta: float, diag: list[float]) -> list[float]:
    return [float(x) + float(delta) * float(d) * float(x) for x, d in zip(g, diag)]


def _norms(g0: list[float], delta: float, diag: list[float], steps: int) -> list[float]:
    g = list(g0)
    norms = [sqrt(sum(float(x) * float(x) for x in g))]
    for _ in range(steps):
        g = _step_euler(g, delta, diag)
        norms.append(sqrt(sum(float(x) * float(x) for x in g)))
    return norms


def test_toy_scale_flow_negative_control_operator_sanity() -> None:
    inp = ScaleFlowInput(
        couplings_init=[1.5],
        delta=0.25,
        n_steps=3,
        scale_init=0.0,
        candidate_id="E1_euler_linear",
        beta_kind="linear_diag",
        beta_diag=[-0.5],
    )
    report = build_toy_scale_flow_report(inp)
    assert report["output"]["diagnostics"]["monotone_flags"]["l2_nonincreasing"] is True

    wrong_norms = _norms([1.5], -0.25, [-0.5], 3)
    wrong_nonincreasing = all(wrong_norms[i + 1] <= wrong_norms[i] + 1e-12 for i in range(len(wrong_norms) - 1))
    assert wrong_nonincreasing is False


def test_toy_scale_flow_negative_control_bad_params() -> None:
    report = build_toy_scale_flow_report(
        ScaleFlowInput(
            couplings_init=[1.9],
            delta=0.2,
            n_steps=2,
            scale_init=0.0,
            candidate_id="E1_euler_linear",
            beta_kind="linear_diag",
            beta_diag=[1.0],
        )
    )

    assert report["admissibility"]["admissible"] is False
    assert "BOUND_EXCEEDED" in report["admissibility"]["reasons"]
