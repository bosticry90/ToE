from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import ov01_fit_family_robustness_gate
from formal.python.toe.observables.ov02_digitization_invariance import ov02_digitization_invariance_gate
from formal.python.toe.observables.ov03_fit_family_robustness import ov03_fit_family_robustness_gate
from formal.python.toe.observables.ovxd02_preference_agreement_record import ovxd02_preference_agreement_record


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


def _load_sample_kw_from_fit_json(path: Path) -> tuple[tuple[float, float], ...]:
    d = _load_json(path)
    if d.get("sample_kw") is None:
        raise AssertionError(f"Missing sample_kw in {path}")
    return tuple((float(k), float(w)) for (k, w) in d["sample_kw"])


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


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise AssertionError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise AssertionError("Missing record fingerprint line")
    return m.group(1)


def test_ov_xd02_preference_agreement_record_matches_current_reports():
    fn = fn01_make_P_cubic_artifact(g=0.3)

    # OV-01g
    base01 = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    lin01 = [
        _load_dr01_fit_from_json(base01 / "dr01_fit_artifact.json"),
        _load_dr01_fit_from_json(base01 / "dr03_fit_artifact.json"),
        _load_dr01_fit_from_json(base01 / "dr04d_fit_artifact.json"),
        _load_dr01_fit_from_json(base01 / "dr05_fit_artifact.json"),
    ]

    curv01 = [
        _load_dr01_fit_curved_from_json(base01 / "dr01_fit_artifact_curved.json"),
        _load_dr01_fit_curved_from_json(base01 / "dr03_fit_artifact_curved.json"),
        _load_dr01_fit_curved_from_json(base01 / "dr04d_fit_artifact_curved.json"),
        _load_dr01_fit_curved_from_json(base01 / "dr05_fit_artifact_curved.json"),
    ]

    rep01 = ov01_fit_family_robustness_gate(fn, lin01, curv01, adequacy_policy="DQ-01_v1")

    # OV-02x
    s02 = _load_sample_kw_from_fit_json(base01 / "dr01_fit_artifact.json")
    s03 = _load_sample_kw_from_fit_json(base01 / "dr03_fit_artifact.json")
    s04d = _load_sample_kw_from_fit_json(base01 / "dr04d_fit_artifact.json")
    s05 = _load_sample_kw_from_fit_json(base01 / "dr05_fit_artifact.json")

    rep02 = ov02_digitization_invariance_gate(
        fn,
        windows_sample_kw=[s02, s03, s04d, s05],
        rel_eps=0.01,
        patterns=("baseline", "alt_pm", "ramp"),
        adequacy_policy="DQ-01_v1",
    )

    # OV-03x
    base03 = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_b1_second_dataset_TBD"

    lin03 = [
        _load_dr01_fit_from_json(base03 / "dr01_fit_artifact.json"),
        _load_dr01_fit_from_json(base03 / "dr03_fit_artifact.json"),
        _load_dr01_fit_from_json(base03 / "dr04d_fit_artifact.json"),
        _load_dr01_fit_from_json(base03 / "dr05_fit_artifact.json"),
    ]

    curv03 = [
        _load_dr01_fit_curved_from_json(base03 / "dr01_fit_artifact_curved.json"),
        _load_dr01_fit_curved_from_json(base03 / "dr03_fit_artifact_curved.json"),
        _load_dr01_fit_curved_from_json(base03 / "dr04d_fit_artifact_curved.json"),
        _load_dr01_fit_curved_from_json(base03 / "dr05_fit_artifact_curved.json"),
    ]

    rep03 = ov03_fit_family_robustness_gate(fn, lin03, curv03, adequacy_policy="DQ-01_v1")

    rec = ovxd02_preference_agreement_record(
        ov01g_report_fingerprint=rep01.fingerprint(),
        ov01g_prefer_curved=rep01.prefer_curved,
        ov01g_robustness_failed=rep01.robustness_failed,
        ov02x_report_fingerprint=rep02.fingerprint(),
        ov02x_all_scenarios_match_baseline=rep02.all_scenarios_match_baseline,
        ov03x_report_fingerprint=rep03.fingerprint(),
        ov03x_prefer_curved=rep03.prefer_curved,
        ov03x_robustness_failed=rep03.robustness_failed,
    )

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-XD-02_cross_dataset_preference_agreement_record.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")

    locked = _extract_json_block(lock_text)

    assert locked["config_tag"] == rec.config_tag
    assert locked["ov01g_report_fingerprint"] == rep01.fingerprint()
    assert locked["ov02x_report_fingerprint"] == rep02.fingerprint()
    assert locked["ov03x_report_fingerprint"] == rep03.fingerprint()
    assert locked["ov01g_preferred_family"] == rec.ov01g_preferred_family
    assert locked["ov03x_preferred_family"] == rec.ov03x_preferred_family
    assert locked["ov02x_all_scenarios_match_baseline"] == rep02.all_scenarios_match_baseline
    assert locked["agreement"] == rec.agreement

    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()

    # Current canonical state records a disagreement.
    assert rec.agreement is False
