from __future__ import annotations

from formal.python.tools.toy_scale_flow_front_door import ScaleFlowInput, build_toy_scale_flow_report


def test_toy_scale_flow_resolution_scan() -> None:
    deltas = [0.25, 0.125, 0.0625]

    for delta in deltas:
        good = build_toy_scale_flow_report(
            ScaleFlowInput(
                couplings_init=[1.5, -1.0],
                delta=delta,
                n_steps=8,
                scale_init=0.0,
                candidate_id="E1_euler_linear",
                beta_kind="linear_diag",
                beta_diag=[-0.5, -0.5],
            )
        )
        assert good["admissibility"]["admissible"] is True
        assert good["output"]["diagnostics"]["monotone_flags"]["l2_nonincreasing"] is True

        bad = build_toy_scale_flow_report(
            ScaleFlowInput(
                couplings_init=[1.5, -1.0],
                delta=delta,
                n_steps=8,
                scale_init=0.0,
                candidate_id="E1_euler_linear",
                beta_kind="linear_diag",
                beta_diag=[1.0, 1.0],
            )
        )
        assert bad["admissibility"]["admissible"] is False
