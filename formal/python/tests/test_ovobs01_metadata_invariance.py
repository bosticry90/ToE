from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.observables.ovobs01_observability_metadata_invariance import (
    ovobs01_metadata_invariance_audit,
)


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _load_dr01_fit_from_json(path: Path) -> DR01Fit1D:
    d = json.loads(path.read_text(encoding="utf-8"))

    sample_kw = None
    if d.get("sample_kw") is not None:
        sample_kw = tuple((float(k), float(w)) for (k, w) in d["sample_kw"])

    return DR01Fit1D(
        u=float(d["u"]),
        c_s=float(d["c_s"]),
        tag=str(d.get("tag", path.name)),
        source_kind=str(d.get("source_kind", "unknown")),
        source_ref=d.get("source_ref", None),
        fit_method_tag=str(d.get("fit_method_tag", "unspecified")),
        data_fingerprint=d.get("data_fingerprint", None),
        sample_kw=sample_kw,
    )


def test_ovobs01_metadata_perturbations_do_not_change_outputs():
    dr_path = (
        REPO_ROOT
        / "formal"
        / "external_evidence"
        / "bec_bragg_steinhauer_2001"
        / "dr01_fit_artifact.json"
    )
    dr = _load_dr01_fit_from_json(dr_path)

    fn = fn01_make_P_cubic_artifact(g=0.4)

    rep = ovobs01_metadata_invariance_audit(fn_artifact=fn, dr_fit_artifact=dr)

    assert rep.ok_obs_value_equal
    assert rep.ok_residual_equal

    # But fingerprints *must* differ because metadata changed.
    assert rep.fn_fingerprint_a != rep.fn_fingerprint_b
    assert rep.dr_fingerprint_a != rep.dr_fingerprint_b
