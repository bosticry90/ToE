from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.dr01_fit_adequacy import dr01_check_curved_fit_adequacy


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


def test_dr01_fit_adequacy_curved_gate_v1_decisions_are_deterministic_and_explainable():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    dr02 = _load_dr01_fit_curved_from_json(base / "dr01_fit_artifact_curved.json")
    dr03 = _load_dr01_fit_curved_from_json(base / "dr03_fit_artifact_curved.json")
    dr04 = _load_dr01_fit_curved_from_json(base / "dr04_fit_artifact_curved.json")
    dr05 = _load_dr01_fit_curved_from_json(base / "dr05_fit_artifact_curved.json")

    rep02 = dr01_check_curved_fit_adequacy(dr02, policy="DQ-01_v1")
    rep03 = dr01_check_curved_fit_adequacy(dr03, policy="DQ-01_v1")
    rep04 = dr01_check_curved_fit_adequacy(dr04, policy="DQ-01_v1")
    rep05 = dr01_check_curved_fit_adequacy(dr05, policy="DQ-01_v1")

    # Determinism
    assert rep02.fingerprint() == dr01_check_curved_fit_adequacy(dr02, policy="DQ-01_v1").fingerprint()

    # Non-brittle decision locks (do not lock exact floats).
    assert rep02.passes is True
    assert rep02.reason_codes == ()

    assert rep03.passes is True
    assert rep03.reason_codes == ()

    # Under default thresholds, DR-04 is underpowered for curved adequacy.
    assert rep04.passes is False
    assert "n_points_lt_min" in rep04.reason_codes
    assert "beta_not_identifiable" in rep04.reason_codes

    assert rep05.passes is True
    assert rep05.reason_codes == ()


def test_dr01_fit_adequacy_curved_gate_v2_allows_low_n_admissible_dr04_and_ignores_beta():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    dr04 = _load_dr01_fit_curved_from_json(base / "dr04_fit_artifact_curved.json")

    rep = dr01_check_curved_fit_adequacy(dr04, policy="DQ-01_v2")

    assert rep.passes is True
    assert rep.reason_codes == ("beta_ignored_low_n",)
    assert rep.metrics.get("beta_used_for_inference") == 0.0


def test_dr01_fit_adequacy_curved_gate_v1_passes_for_dr04d_min_n5_window():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    dr04d = _load_dr01_fit_curved_from_json(base / "dr04d_fit_artifact_curved.json")

    rep = dr01_check_curved_fit_adequacy(dr04d, policy="DQ-01_v1")

    assert rep.passes is True
    assert rep.reason_codes == ()


def test_dr01_fit_adequacy_curved_gate_variantA_allows_only_dr04_n4_with_strict_bounds_and_beta_ignored():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    dr04 = _load_dr01_fit_curved_from_json(base / "dr04_fit_artifact_curved.json")

    rep = dr01_check_curved_fit_adequacy(dr04, policy="DQ-01_variantA")

    assert rep.passes is True
    assert rep.metrics.get("beta_used_for_inference") == 0.0
    assert "beta_ignored_low_n" in rep.reason_codes
    assert float(rep.metrics.get("rmse_omega_over_k_m_per_s")) <= 2.50e-4
    assert float(rep.metrics.get("c0_stderr_m_per_s")) <= 2.80e-4
    assert "beta_not_identifiable" not in rep.reason_codes
