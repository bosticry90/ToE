from __future__ import annotations

from formal.python.tools.toy_stochastic_selection_report_generate import (
    build_toy_stochastic_selection_report_payload,
    render_toy_stochastic_selection_report_text,
)


def test_toy_stochastic_selection_report_is_deterministic() -> None:
    r1 = build_toy_stochastic_selection_report_payload()
    r2 = build_toy_stochastic_selection_report_payload()

    assert r1 == r2
    assert r1.get("schema") == "TOY/stochastic_selection_report/v1"
    assert r1.get("schema_version") == "v1"
    assert r1.get("candidate_id") == "F1_noise_plus_pullback"
    assert isinstance(r1.get("fingerprint"), str) and len(r1["fingerprint"]) == 64

    t1 = render_toy_stochastic_selection_report_text(r1)
    t2 = render_toy_stochastic_selection_report_text(r2)
    assert t1 == t2
