from __future__ import annotations

from formal.python.tools.toy_topological_invariants_report_generate import (
    build_toy_topological_invariants_report_payload,
    render_toy_topological_invariants_report_text,
)


def test_toy_topological_invariants_report_is_deterministic() -> None:
    r1 = build_toy_topological_invariants_report_payload()
    r2 = build_toy_topological_invariants_report_payload()

    assert r1 == r2
    assert r1.get("schema") == "TOY/topological_invariants_report/v1"
    assert r1.get("candidate_id") == "G1_sign_change"
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64

    t1 = render_toy_topological_invariants_report_text(r1)
    t2 = render_toy_topological_invariants_report_text(r2)
    assert t1 == t2
