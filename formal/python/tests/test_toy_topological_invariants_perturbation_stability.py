from __future__ import annotations

from formal.python.tools.toy_topological_invariants_front_door import (
    TopologicalStateInput,
    ToyGInput,
    ToyGParams,
    build_toy_topological_invariants_report,
)


def _defect_count(report: dict) -> int:
    return int(report["output"]["defects_before"]["count"])


def test_toy_topological_invariants_perturbation_stability() -> None:
    base_grid = [1.2, 0.8, -0.9, -1.1, 1.4]
    perturbed_grid = [x + 0.01 for x in base_grid]

    base_report = build_toy_topological_invariants_report(
        ToyGInput(
            state=TopologicalStateInput(grid=base_grid),
            params=ToyGParams(step_size=0.2, detector_id="sign_change", threshold=0.0),
            candidate_id="G1_sign_change",
        )
    )
    perturbed_report = build_toy_topological_invariants_report(
        ToyGInput(
            state=TopologicalStateInput(grid=perturbed_grid),
            params=ToyGParams(step_size=0.2, detector_id="sign_change", threshold=0.0),
            candidate_id="G1_sign_change",
        )
    )

    assert _defect_count(base_report) == _defect_count(perturbed_report)

    assert base_report["output"]["defects_before"]["count"] == base_report["output"]["defects_after"]["count"]
    assert perturbed_report["output"]["defects_before"]["count"] == perturbed_report["output"]["defects_after"]["count"]
