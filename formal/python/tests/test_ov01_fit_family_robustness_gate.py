from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import ov01_fit_family_robustness_gate


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


def test_ov01_fit_family_robustness_gate_v1_prefers_curved_for_dr04d_min_n5_set():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    # Linear DR windows
    dr02 = _load_dr01_fit_from_json(base / "dr01_fit_artifact.json")
    dr03 = _load_dr01_fit_from_json(base / "dr03_fit_artifact.json")
    dr04d_lin = _load_dr01_fit_from_json(base / "dr04d_fit_artifact.json")
    dr05 = _load_dr01_fit_from_json(base / "dr05_fit_artifact.json")

    # Curved DR windows
    dr02c = _load_dr01_fit_curved_from_json(base / "dr01_fit_artifact_curved.json")
    dr03c = _load_dr01_fit_curved_from_json(base / "dr03_fit_artifact_curved.json")
    dr04d = _load_dr01_fit_curved_from_json(base / "dr04d_fit_artifact_curved.json")
    dr05c = _load_dr01_fit_curved_from_json(base / "dr05_fit_artifact_curved.json")

    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep = ov01_fit_family_robustness_gate(
        fn,
        [dr02, dr03, dr04d_lin, dr05],
        [dr02c, dr03c, dr04d, dr05c],
        adequacy_policy="DQ-01_v1",
    )

    # Determinism
    assert rep.fingerprint() == ov01_fit_family_robustness_gate(
        fn,
        [dr02, dr03, dr04d_lin, dr05],
        [dr02c, dr03c, dr04d, dr05c],
        adequacy_policy="DQ-01_v1",
    ).fingerprint()

    # Minimal, non-brittle decision locks.
    assert rep.adequacy_policy == "DQ-01_v1"
    assert rep.r_max_curved < rep.r_max_linear
    assert rep.q_ratio <= rep.q_threshold
    assert rep.curved_adequacy_passes is True
    assert rep.prefer_curved is True
    assert rep.robustness_failed is False


def test_ov01_fit_family_robustness_gate_v2_prefers_curved_for_dr04d_min_n5_set():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    # Linear DR windows
    dr02 = _load_dr01_fit_from_json(base / "dr01_fit_artifact.json")
    dr03 = _load_dr01_fit_from_json(base / "dr03_fit_artifact.json")
    dr04d_lin = _load_dr01_fit_from_json(base / "dr04d_fit_artifact.json")
    dr05 = _load_dr01_fit_from_json(base / "dr05_fit_artifact.json")

    # Curved DR windows
    dr02c = _load_dr01_fit_curved_from_json(base / "dr01_fit_artifact_curved.json")
    dr03c = _load_dr01_fit_curved_from_json(base / "dr03_fit_artifact_curved.json")
    dr04d = _load_dr01_fit_curved_from_json(base / "dr04d_fit_artifact_curved.json")
    dr05c = _load_dr01_fit_curved_from_json(base / "dr05_fit_artifact_curved.json")

    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep = ov01_fit_family_robustness_gate(
        fn,
        [dr02, dr03, dr04d_lin, dr05],
        [dr02c, dr03c, dr04d, dr05c],
        adequacy_policy="DQ-01_v2",
    )

    # Minimal, non-brittle decision locks.
    assert rep.adequacy_policy == "DQ-01_v2"
    assert rep.r_max_curved < rep.r_max_linear
    assert rep.q_ratio <= rep.q_threshold
    assert rep.curved_adequacy_passes is True
    assert rep.prefer_curved is True
    assert rep.robustness_failed is False


def test_ov01_fit_family_robustness_gate_v1_is_undecided_for_legacy_dr04a_set():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    # Linear DR windows (legacy)
    dr02 = _load_dr01_fit_from_json(base / "dr01_fit_artifact.json")
    dr03 = _load_dr01_fit_from_json(base / "dr03_fit_artifact.json")
    dr04 = _load_dr01_fit_from_json(base / "dr04_fit_artifact.json")
    dr05 = _load_dr01_fit_from_json(base / "dr05_fit_artifact.json")

    # Curved DR windows (legacy)
    dr02c = _load_dr01_fit_curved_from_json(base / "dr01_fit_artifact_curved.json")
    dr03c = _load_dr01_fit_curved_from_json(base / "dr03_fit_artifact_curved.json")
    dr04c = _load_dr01_fit_curved_from_json(base / "dr04_fit_artifact_curved.json")
    dr05c = _load_dr01_fit_curved_from_json(base / "dr05_fit_artifact_curved.json")

    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep = ov01_fit_family_robustness_gate(
        fn,
        [dr02, dr03, dr04, dr05],
        [dr02c, dr03c, dr04c, dr05c],
        adequacy_policy="DQ-01_v1",
    )

    assert rep.r_max_curved < rep.r_max_linear
    assert rep.q_ratio <= rep.q_threshold
    assert rep.curved_adequacy_passes is False
    assert rep.prefer_curved is False
    assert rep.robustness_failed is True


def test_ov01_fit_family_robustness_gate_variantA_prefers_curved_for_legacy_dr04a_set_when_dr04_is_admitted():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    # Linear DR windows (legacy)
    dr02 = _load_dr01_fit_from_json(base / "dr01_fit_artifact.json")
    dr03 = _load_dr01_fit_from_json(base / "dr03_fit_artifact.json")
    dr04 = _load_dr01_fit_from_json(base / "dr04_fit_artifact.json")
    dr05 = _load_dr01_fit_from_json(base / "dr05_fit_artifact.json")

    # Curved DR windows (legacy)
    dr02c = _load_dr01_fit_curved_from_json(base / "dr01_fit_artifact_curved.json")
    dr03c = _load_dr01_fit_curved_from_json(base / "dr03_fit_artifact_curved.json")
    dr04c = _load_dr01_fit_curved_from_json(base / "dr04_fit_artifact_curved.json")
    dr05c = _load_dr01_fit_curved_from_json(base / "dr05_fit_artifact_curved.json")

    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep = ov01_fit_family_robustness_gate(
        fn,
        [dr02, dr03, dr04, dr05],
        [dr02c, dr03c, dr04c, dr05c],
        adequacy_policy="DQ-01_variantA",
    )

    assert rep.adequacy_policy == "DQ-01_variantA"
    assert rep.r_max_curved < rep.r_max_linear
    assert rep.q_ratio <= rep.q_threshold
    assert rep.curved_adequacy_passes is True
    assert rep.prefer_curved is True
    assert rep.robustness_failed is False
