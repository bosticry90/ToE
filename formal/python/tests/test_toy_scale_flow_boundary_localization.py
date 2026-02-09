from __future__ import annotations

from formal.python.tools.toy_scale_flow_front_door import ScaleFlowInput, build_toy_scale_flow_report


def test_toy_scale_flow_boundary_localization() -> None:
    pass_case = build_toy_scale_flow_report(
        ScaleFlowInput(
            couplings_init=[1.6, 0.1],
            delta=0.2,
            n_steps=1,
            scale_init=0.0,
            candidate_id="E1_euler_linear",
            beta_kind="linear_diag",
            beta_diag=[1.0, 0.0],
        )
    )

    assert pass_case["admissibility"]["admissible"] is True
    assert pass_case["admissibility"]["violations"] == []

    fail_case = build_toy_scale_flow_report(
        ScaleFlowInput(
            couplings_init=[1.9, 0.1],
            delta=0.2,
            n_steps=1,
            scale_init=0.0,
            candidate_id="E1_euler_linear",
            beta_kind="linear_diag",
            beta_diag=[1.0, 0.0],
        )
    )

    assert fail_case["admissibility"]["admissible"] is False
    violations = list(fail_case["admissibility"]["violations"])
    assert len(violations) == 1
    v0 = violations[0]
    assert v0["step"] == 1
    assert v0["index"] == 0
