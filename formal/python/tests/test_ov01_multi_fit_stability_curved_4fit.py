from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov01_multi_fit_stability_curved import ov01_multi_fit_stability_curved


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_dr01_fit_curved_from_json(path: Path) -> DR01FitCurved1D:
    d = _load_json(path)

    sample_kw = None
    if d.get("sample_kw") is not None:
        sample_kw = tuple((float(k), float(w)) for (k, w) in d["sample_kw"])

    fq = None
    if d.get("fit_quality") is not None:
        q = d["fit_quality"]
        fq = DR01FitQualityCurved1D(
            n_points=int(q["n_points"]),
            rmse_omega_over_k_m_per_s=float(q["rmse_omega_over_k_m_per_s"]),
            c0_stderr_m_per_s=float(q["c0_stderr_m_per_s"]),
            beta_stderr_s_per_m2=float(q["beta_stderr_s_per_m2"]),
            r2_y_space=float(q["r2_y_space"]),
        )

    return DR01FitCurved1D(
        u=float(d["u"]),
        c0=float(d["c0"]),
        beta=float(d["beta"]),
        tag=str(d.get("tag", path.name)),
        source_kind=str(d.get("source_kind", "unknown")),
        source_ref=d.get("source_ref", None),
        data_fingerprint=d.get("data_fingerprint", None),
        sample_kw=sample_kw,
        fit_method_tag=str(d.get("fit_method_tag", "unspecified")),
        fit_quality=fq,
        fit_quality_fingerprint=d.get("fit_quality_fingerprint", None),
    )


def test_ov01_multi_fit_stability_curved_4fit_lock():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    dr02 = _load_dr01_fit_curved_from_json(base / "dr01_fit_artifact_curved.json")
    dr03 = _load_dr01_fit_curved_from_json(base / "dr03_fit_artifact_curved.json")
    dr04 = _load_dr01_fit_curved_from_json(base / "dr04_fit_artifact_curved.json")
    dr05 = _load_dr01_fit_curved_from_json(base / "dr05_fit_artifact_curved.json")

    fn0 = fn01_make_P_cubic_artifact(g=0.0)
    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep0 = ov01_multi_fit_stability_curved(fn0, [dr02, dr03, dr04, dr05], tau_obs=0.10)
    rep = ov01_multi_fit_stability_curved(fn, [dr02, dr03, dr04, dr05], tau_obs=0.10)

    # Determinism
    assert rep.fingerprint() == ov01_multi_fit_stability_curved(fn, [dr02, dr03, dr04, dr05], tau_obs=0.10).fingerprint()

    # Degenerate g=0 case should yield obs=0 for all and thus all residuals 0.
    assert rep0.obs_values == (0.0, 0.0, 0.0, 0.0)
    assert rep0.r_max == 0.0
    assert rep0.r_rms == 0.0

    # Lock rough expected values (computed deterministically from the same sample_kw).
    assert rep.retain is False
    assert abs(rep.r_max - 0.2296947) < 5.0e-4
    assert abs(rep.r_rms - 0.1528807) < 5.0e-4
