from __future__ import annotations

from formal.python.tools.toy_topological_invariants_front_door import (
    TopologicalStateInput,
    ToyGInput,
    ToyGParams,
    build_toy_topological_invariants_report,
)


def _defect_count(report: dict) -> int:
    return int(report["output"]["defects_before"]["count"])


def test_toy_topological_invariants_resolution_scan() -> None:
    sizes = [5, 7, 9]

    pass_results = []
    fail_results = []
    for n in sizes:
        pass_grid = [1.0] * n
        fail_grid = [1.0 if (i % 2 == 0) else -1.0 for i in range(n)]

        pass_report = build_toy_topological_invariants_report(
            ToyGInput(
                state=TopologicalStateInput(grid=pass_grid),
                params=ToyGParams(step_size=0.2, detector_id="sign_change", threshold=0.0),
                candidate_id="G1_sign_change",
            )
        )
        fail_report = build_toy_topological_invariants_report(
            ToyGInput(
                state=TopologicalStateInput(grid=fail_grid),
                params=ToyGParams(step_size=0.2, detector_id="sign_change", threshold=0.0),
                candidate_id="G1_sign_change",
            )
        )

        pass_results.append(_defect_count(pass_report) == 0)
        fail_results.append(_defect_count(fail_report) == 0)

    assert all(pass_results)
    assert not any(fail_results)
