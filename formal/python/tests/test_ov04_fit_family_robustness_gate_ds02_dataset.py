from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov04_fit_family_robustness_lowk_ds02 import ov04_fit_family_robustness_gate


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


def _load_dr01_fit_from_json(path: Path) -> DR01Fit1D:
    d = _load_json(path)

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


def test_ov04_fit_family_robustness_gate_skips_until_ds02_artifacts_exist():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_ds02_lowk_dataset_TBD"

    required = [
        base / "dr01_fit_artifact.json",
        base / "dr01_fit_artifact_curved.json",
        base / "dr03_fit_artifact.json",
        base / "dr03_fit_artifact_curved.json",
        base / "dr04d_fit_artifact.json",
        base / "dr04d_fit_artifact_curved.json",
        base / "dr05_fit_artifact.json",
        base / "dr05_fit_artifact_curved.json",
    ]

    if not all(p.exists() for p in required):
        pytest.skip("DS-02 dataset DR artifacts not yet generated")

    dr02 = _load_dr01_fit_from_json(base / "dr01_fit_artifact.json")
    dr03 = _load_dr01_fit_from_json(base / "dr03_fit_artifact.json")
    dr04d = _load_dr01_fit_from_json(base / "dr04d_fit_artifact.json")
    dr05 = _load_dr01_fit_from_json(base / "dr05_fit_artifact.json")

    dr02c = _load_dr01_fit_curved_from_json(base / "dr01_fit_artifact_curved.json")
    dr03c = _load_dr01_fit_curved_from_json(base / "dr03_fit_artifact_curved.json")
    dr04dc = _load_dr01_fit_curved_from_json(base / "dr04d_fit_artifact_curved.json")
    dr05c = _load_dr01_fit_curved_from_json(base / "dr05_fit_artifact_curved.json")

    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep = ov04_fit_family_robustness_gate(
        fn,
        [dr02, dr03, dr04d, dr05],
        [dr02c, dr03c, dr04dc, dr05c],
        adequacy_policy="DQ-01_v1",
    )

    assert rep.fingerprint() == ov04_fit_family_robustness_gate(
        fn,
        [dr02, dr03, dr04d, dr05],
        [dr02c, dr03c, dr04dc, dr05c],
        adequacy_policy="DQ-01_v1",
    ).fingerprint()
