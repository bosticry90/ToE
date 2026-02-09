from __future__ import annotations

import json

import pytest

from formal.python.toe.observables.ovucff01_jitter_structure_audit import (
    ovucff01_jitter_structure_audit,
    ucff_dispersion_omega2_first_order,
    ucff_dispersion_omega2_second_order,
    ucff_symbolic_symbols,
    write_ovucff01_jitter_structure_artifact,
)


def test_symbolic_structure_has_expected_terms() -> None:
    s = ucff_symbolic_symbols()
    k = s["k"]

    o1 = ucff_dispersion_omega2_first_order().expand()
    o2 = ucff_dispersion_omega2_second_order().expand()

    assert o1.has(k**2)
    assert o1.has(k**4)
    assert not o1.has(k**6)

    assert o2.has(k**2)
    assert o2.has(k**4)
    assert o2.has(k**6)


def test_jitter_audit_is_deterministic_for_seed() -> None:
    rep1 = ovucff01_jitter_structure_audit(seed=7, n_jitters=25, jitter_frac=0.01, k_max=4.0, n_k=51)
    rep2 = ovucff01_jitter_structure_audit(seed=7, n_jitters=25, jitter_frac=0.01, k_max=4.0, n_k=51)

    assert rep1.to_jsonable() == rep2.to_jsonable()
    assert rep1.n_stable + rep1.n_unstable == 25


def test_artifact_write_json(tmp_path) -> None:
    out = tmp_path / "ucff_jitter_structure.json"
    wrote = write_ovucff01_jitter_structure_artifact(path=out, seed=1, n_jitters=3, jitter_frac=0.0, k_max=2.0, n_k=11)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-UCFF-01/jitter_structure_artifact/v1"
    assert "fingerprint" in payload
    assert "report" in payload

    report = payload["report"]
    assert report["schema"] == "OV-UCFF-01/jitter_structure_report/v1"
    assert report["n_unstable"] == 0
