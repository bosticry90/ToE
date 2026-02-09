from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.observables.ov01_multi_fit_stability import ov01_multi_fit_stability


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


def test_ov01_multi_fit_stability_4fit_lock_and_monotone_drift_envelope():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    dr02 = _load_dr01_fit_from_json(base / "dr01_fit_artifact.json")
    dr03 = _load_dr01_fit_from_json(base / "dr03_fit_artifact.json")
    dr04 = _load_dr01_fit_from_json(base / "dr04_fit_artifact.json")
    dr05 = _load_dr01_fit_from_json(base / "dr05_fit_artifact.json")

    fn0 = fn01_make_P_cubic_artifact(g=0.0)
    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep0 = ov01_multi_fit_stability(fn0, [dr02, dr03, dr04, dr05], epsilon=1e-12, tau_obs=0.10)
    rep = ov01_multi_fit_stability(fn, [dr02, dr03, dr04, dr05], epsilon=1e-12, tau_obs=0.10)

    # Fingerprint propagation
    assert rep.fn_fingerprint == fn.fingerprint()
    assert rep.dr_fingerprints == (dr02.fingerprint(), dr03.fingerprint(), dr04.fingerprint(), dr05.fingerprint())

    # Determinism
    assert rep.fingerprint() == ov01_multi_fit_stability(fn, [dr02, dr03, dr04, dr05], epsilon=1e-12, tau_obs=0.10).fingerprint()

    # Degenerate g=0 case should yield obs=0 for all and thus all residuals 0.
    assert rep0.obs_values == (0.0, 0.0, 0.0, 0.0)
    assert rep0.r_max == 0.0
    assert rep0.r_rms == 0.0

    # Lock expected summary statistics for this specific DR02/DR03/DR04/DR05 quartet.
    assert abs(rep.r_max - 0.29003318302945985) < 1e-15
    assert abs(rep.r_rms - 0.1847750479626659) < 1e-15
