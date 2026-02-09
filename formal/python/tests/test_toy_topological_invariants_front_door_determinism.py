from __future__ import annotations

from formal.python.tools.toy_topological_invariants_front_door import (
    SCHEMA_ID,
    TopologicalStateInput,
    ToyGInput,
    ToyGParams,
    build_toy_topological_invariants_report,
)


def test_toy_topological_invariants_front_door_is_deterministic() -> None:
    inp = ToyGInput(
        state=TopologicalStateInput(grid=[1.0, -1.0, 1.0, -1.0]),
        params=ToyGParams(step_size=0.2, detector_id="sign_change", threshold=0.0),
        candidate_id="G1_sign_change",
    )

    r1 = build_toy_topological_invariants_report(inp)
    r2 = build_toy_topological_invariants_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert r1["candidate_id"] == "G1_sign_change"
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
