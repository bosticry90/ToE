from __future__ import annotations

from formal.python.tools.toy_coherence_transport_front_door import (
    SCHEMA_ID,
    CoherenceInput,
    SubstrateInput,
    ToyBInput,
    ToyBParams,
    build_toy_coherence_report,
)


def test_toy_coherence_transport_front_door_is_deterministic() -> None:
    inp = ToyBInput(
        substrate=SubstrateInput(value=1.0),
        coherence=CoherenceInput(value=2.05),
        params=ToyBParams(dt=0.02, alpha=0.0, beta=1.0, source_bias=0.0),
    )

    r1 = build_toy_coherence_report(inp)
    r2 = build_toy_coherence_report(inp)

    assert r1 == r2
    assert r1["schema"] == SCHEMA_ID
    assert isinstance(r1.get("input_fingerprint"), str) and len(r1["input_fingerprint"]) == 64
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64
