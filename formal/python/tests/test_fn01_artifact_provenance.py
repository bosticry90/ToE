from __future__ import annotations

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact


def test_fn01_artifact_provenance_and_determinism():
    a = fn01_make_P_cubic_artifact(g=0.3, source_kind="manual", source_ref="unit_test")

    assert a.source_kind != "unknown"
    assert a.candidate_tag in {"P_cubic"}

    fp0 = a.fingerprint()
    fp1 = a.fingerprint()
    assert fp0 == fp1

    b = fn01_make_P_cubic_artifact(g=0.3000001, source_kind="manual", source_ref="unit_test")
    assert b.fingerprint() != fp0

    c = fn01_make_P_cubic_artifact(g=0.3, source_kind="manual", source_ref="different_ref")
    assert c.fingerprint() != fp0
