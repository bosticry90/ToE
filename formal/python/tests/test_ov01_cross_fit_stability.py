from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.observables.ov01_cross_fit_stability import ov01_cross_fit_stability


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


def test_ov01_cross_fit_stability_fingerprints_and_non_degeneracy_lock():
    dr02_path = (
        REPO_ROOT
        / "formal"
        / "external_evidence"
        / "bec_bragg_steinhauer_2001"
        / "dr01_fit_artifact.json"
    )
    dr03_path = (
        REPO_ROOT
        / "formal"
        / "external_evidence"
        / "bec_bragg_steinhauer_2001"
        / "dr03_fit_artifact.json"
    )

    dr02 = _load_dr01_fit_from_json(dr02_path)
    dr03 = _load_dr01_fit_from_json(dr03_path)

    # Grid includes a degenerate g=0 case and a non-degenerate g>0 case.
    fn0 = fn01_make_P_cubic_artifact(g=0.0)
    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep0 = ov01_cross_fit_stability(fn0, dr02, dr03, epsilon=1e-12, tau_obs=0.10)
    rep = ov01_cross_fit_stability(fn, dr02, dr03, epsilon=1e-12, tau_obs=0.10)

    # Fingerprint propagation
    assert rep.fn_fingerprint == fn.fingerprint()
    assert rep.dr02_fingerprint == dr02.fingerprint()
    assert rep.dr03_fingerprint == dr03.fingerprint()

    # Determinism of report fingerprint
    assert rep.fingerprint() == ov01_cross_fit_stability(fn, dr02, dr03, epsilon=1e-12, tau_obs=0.10).fingerprint()

    # Non-degeneracy guardrail:
    # If the two DR artifacts differ (fingerprints differ) and FN is not degenerate (g != 0),
    # then the cross-fit residual must be strictly positive unless the metrics are exactly equal.
    if rep.dr02_fingerprint != rep.dr03_fingerprint and rep.obs_02 != 0.0:
        if rep.metric02_fingerprint != rep.metric03_fingerprint:
            assert rep.r_obs_cross > 0.0

    # Degenerate g=0 case should yield obs=0 on both and thus residual 0.
    assert rep0.obs_02 == 0.0
    assert rep0.obs_03 == 0.0
    assert rep0.r_obs_cross == 0.0
