"""OV-XD-02: lock writer for cross-dataset preference agreement record.

This module performs filesystem I/O to compute current report fingerprints from
frozen artifacts, then writes the canonical markdown lock.

Design intent
- Keep `ovxd02_preference_agreement_record.py` pure (no I/O).
- Make the lock match the computed record used by tests.
"""

from __future__ import annotations

from dataclasses import asdict
import hashlib
import json
from pathlib import Path

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import ov01_fit_family_robustness_gate
from formal.python.toe.observables.ov02_digitization_invariance import ov02_digitization_invariance_gate
from formal.python.toe.observables.ov03_fit_family_robustness import ov03_fit_family_robustness_gate
from formal.python.toe.observables.ovxd02_preference_agreement_record import (
    OVXD02PreferenceAgreementRecord,
    ovxd02_preference_agreement_record,
)


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_sample_kw_from_fit_json(path: Path) -> tuple[tuple[float, float], ...]:
    d = _load_json(path)
    sample_kw = d.get("sample_kw")
    if sample_kw is None:
        raise ValueError(f"Missing sample_kw in fit artifact: {path.as_posix()}")
    return tuple((float(k), float(w)) for (k, w) in sample_kw)


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


def compute_ovxd02_record(*, repo_root: Path | None = None) -> OVXD02PreferenceAgreementRecord:
    repo_root = _find_repo_root(Path(__file__)) if repo_root is None else Path(repo_root)

    fn = fn01_make_P_cubic_artifact(g=0.3)

    # OV-01g / OV-02x use the Steinhauer 2001 frozen artifacts.
    base01 = repo_root / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

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

    # OV-03x uses the B1 second dataset frozen artifacts.
    base03 = repo_root / "formal" / "external_evidence" / "bec_bragg_b1_second_dataset_TBD"

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

    return ovxd02_preference_agreement_record(
        ov01g_report_fingerprint=rep01.fingerprint(),
        ov01g_prefer_curved=rep01.prefer_curved,
        ov01g_robustness_failed=rep01.robustness_failed,
        ov02x_report_fingerprint=rep02.fingerprint(),
        ov02x_all_scenarios_match_baseline=rep02.all_scenarios_match_baseline,
        ov03x_report_fingerprint=rep03.fingerprint(),
        ov03x_prefer_curved=rep03.prefer_curved,
        ov03x_robustness_failed=rep03.robustness_failed,
    )


def render_ovxd02_lock_markdown(record: OVXD02PreferenceAgreementRecord) -> str:
    payload = asdict(record)
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-XD-02 — Cross-dataset preference agreement record (computed)\n\n"
        "Purpose\n"
        "- Deterministically record whether robustness-only preferred-fit-family outcomes agree across datasets.\n\n"
        "Scope / limits\n"
        "- Record only; no physics claim.\n"
        "- Must not be used for β inference.\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{record.fingerprint()}`\n"
    )


def write_ovxd02_lock(*, lock_path: Path | None = None) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-XD-02_cross_dataset_preference_agreement_record.md"
        )

    rec = compute_ovxd02_record(repo_root=repo_root)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovxd02_lock_markdown(rec), encoding="utf-8")
    return out


def lock_payload_fingerprint(*, repo_root: Path | None = None) -> str:
    """Convenience: stable fingerprint of the lock JSON payload."""
    rec = compute_ovxd02_record(repo_root=repo_root)
    return _sha256_json(asdict(rec))
