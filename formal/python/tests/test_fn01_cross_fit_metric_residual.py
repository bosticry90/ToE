from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.constraints.fn01_metric_discriminator import fn01_cross_fit_metric_residual
from formal.python.toe.dr01_fit import DR01Fit1D


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

    # Ignore any extra keys (e.g. embedded BR-01 outputs) to keep this a DR-01 artifact load.
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


def test_fn01_cross_fit_metric_residual_fingerprints_and_positivity_lock():
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

    fn = fn01_make_P_cubic_artifact(g=0.3)

    report = fn01_cross_fit_metric_residual(fn, dr02, dr03, epsilon=1e-12)

    assert report.fn_fingerprint == fn.fingerprint()
    assert report.dr02_fingerprint == dr02.fingerprint()
    assert report.dr03_fingerprint == dr03.fingerprint()

    assert report.r_metric >= 0.0

    # Critical metric-sensitivity lock:
    # If BR-01 produces different g_tt under the two fit choices, residual must be strictly positive.
    if report.g_tt_02 != report.g_tt_03:
        assert report.r_metric > 0.0
    else:
        # If the pipeline produces equal metrics, lock that as a finding.
        assert report.r_metric == 0.0
