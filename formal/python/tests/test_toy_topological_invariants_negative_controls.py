from __future__ import annotations

from formal.python.tools.toy_topological_invariants_front_door import (
    TopologicalStateInput,
    ToyGInput,
    ToyGParams,
    build_toy_topological_invariants_report,
)


def _sign_change_count(values: list[float]) -> int:
    signs = []
    for x in values:
        if x > 0.0:
            signs.append(1)
        elif x < 0.0:
            signs.append(-1)
        else:
            signs.append(0)
    count = 0
    for i in range(len(signs) - 1):
        if signs[i] == 0 or signs[i + 1] == 0:
            continue
        if signs[i] != signs[i + 1]:
            count += 1
    return count


def test_toy_topological_invariants_negative_control_wrong_detector() -> None:
    grid = [1.0, -1.0, 1.0, -1.0]

    sign_report = build_toy_topological_invariants_report(
        ToyGInput(
            state=TopologicalStateInput(grid=grid),
            params=ToyGParams(step_size=0.2, detector_id="sign_change", threshold=0.0),
            candidate_id="G1_sign_change",
        )
    )
    threshold_report = build_toy_topological_invariants_report(
        ToyGInput(
            state=TopologicalStateInput(grid=grid),
            params=ToyGParams(step_size=0.2, detector_id="threshold_count", threshold=0.0),
            candidate_id="G1_sign_change",
        )
    )

    assert sign_report["output"]["defects_before"]["count"] != threshold_report["output"]["defects_before"]["count"]


def test_toy_topological_invariants_negative_control_wrong_update() -> None:
    grid = [1.0, -1.0, 1.0, -1.0]

    report = build_toy_topological_invariants_report(
        ToyGInput(
            state=TopologicalStateInput(grid=grid),
            params=ToyGParams(step_size=0.2, detector_id="sign_change", threshold=0.0),
            candidate_id="G1_sign_change",
        )
    )

    wrong_updated = [max(0.0, x) for x in grid]
    wrong_count = _sign_change_count(wrong_updated)

    assert int(report["output"]["defects_before"]["count"]) != wrong_count
