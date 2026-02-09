"""OV-04x: deterministic lock writer for DS-02 low-k robustness-only evaluation.

This module performs filesystem I/O to load the frozen DS-02 artifacts and
renders a canonical markdown lock containing:
- The OV-04x robustness gate JSON payload.
- A deterministic report fingerprint.

Scope / limits
- Robustness-only selector evaluation; no physics claim.
- β-null posture: β not inferred / compatible with 0.
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
from formal.python.toe.observables.ov01_fit_family_robustness import OV01FitFamilyRobustnessReport
from formal.python.toe.observables.ov04_fit_family_robustness_lowk_ds02 import ov04_fit_family_robustness_gate


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


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


def ov04x_fit_family_robustness_report(
    *,
    repo_root: Path | None = None,
    adequacy_policy: str = "DQ-01_v1",
    q_threshold: float = 0.90,
    config_tag: str = "OV-04x_fit_family_robustness_v1",
) -> OV01FitFamilyRobustnessReport:
    """Compute OV-04x robustness report from frozen DS-02 artifacts."""

    repo_root = _find_repo_root(Path(__file__)) if repo_root is None else Path(repo_root)
    ds02_dir = repo_root / "formal" / "external_evidence" / "bec_bragg_ds02_lowk_dataset_TBD"

    lin_paths = [
        ds02_dir / "dr01_fit_artifact.json",
        ds02_dir / "dr03_fit_artifact.json",
        ds02_dir / "dr04d_fit_artifact.json",
        ds02_dir / "dr05_fit_artifact.json",
    ]
    curv_paths = [
        ds02_dir / "dr01_fit_artifact_curved.json",
        ds02_dir / "dr03_fit_artifact_curved.json",
        ds02_dir / "dr04d_fit_artifact_curved.json",
        ds02_dir / "dr05_fit_artifact_curved.json",
    ]

    dr_lin = [_load_dr01_fit_from_json(p) for p in lin_paths]
    dr_curv = [_load_dr01_fit_curved_from_json(p) for p in curv_paths]

    fn = fn01_make_P_cubic_artifact(g=0.3)

    return ov04_fit_family_robustness_gate(
        fn,
        dr_lin,
        dr_curv,
        adequacy_policy=str(adequacy_policy),
        q_threshold=float(q_threshold),
        config_tag=str(config_tag),
    )


def _report_to_jsonable(report: OV01FitFamilyRobustnessReport) -> dict:
    d = asdict(report)
    # Ensure JSONable primitives.
    for k in list(d.keys()):
        v = d[k]
        if isinstance(v, float):
            d[k] = float(v)
        elif isinstance(v, bool):
            d[k] = bool(v)
        elif isinstance(v, str):
            d[k] = str(v)
    return d


def render_ov04x_lock_markdown(
    *,
    repo_root: Path | None = None,
    adequacy_policy: str = "DQ-01_v1",
    q_threshold: float = 0.90,
    config_tag: str | None = None,
) -> str:
    repo_root = _find_repo_root(Path(__file__)) if repo_root is None else Path(repo_root)
    ds02_dir = repo_root / "formal" / "external_evidence" / "bec_bragg_ds02_lowk_dataset_TBD"
    csv_path = ds02_dir / "omega_k_data.csv"

    csv_sha = _sha256_file(csv_path)
    # Count rows (exclude header).
    rows = sum(1 for _ in csv_path.read_text(encoding="utf-8").splitlines()[1:] if _.strip() != "")

    effective_tag = "OV-04x_fit_family_robustness_v1" if config_tag is None else str(config_tag)
    rep = ov04x_fit_family_robustness_report(
        repo_root=repo_root,
        adequacy_policy=str(adequacy_policy),
        q_threshold=float(q_threshold),
        config_tag=str(effective_tag),
    )
    payload = _report_to_jsonable(rep)
    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-04x — Fit-family robustness on DS-02 low-k external dataset (locked)\n\n"
        "This lock records the **DS-02 low-k external dataset** robustness-only evaluation.\n\n"
        "Scope / limits\n"
        "- Low-k dataset; does not generalize; no continuity claim.\n"
        "- Robustness-only; no physics claim.\n"
        "- β-null posture: β not inferred / compatible with 0.\n\n"
        "Source (designated)\n"
        "- Shammass et al. (2012), arXiv:1207.3440v2\n"
        "- Local PDF: `formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/1207.3440v2.pdf`\n"
        "- Figure: Fig. 2 (ω_k/2π vs k)\n\n"
        "Digitization / units\n\n"
        "- CSV: `formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv`\n"
        f"\t- sha256: `{csv_sha}`\n"
        f"\t- rows: {rows}\n"
        "- Series selection: Fig. 2 **filled circles** only (ignore open circles).\n\n"
        "Window artifacts used (deterministic)\n\n"
        "All artifacts are generated via `formal/python/tools/generate_ds02_dr_artifacts.py` from the frozen CSV.\n\n"
        "- Linear (through-origin) artifacts: dr01/dr03/dr04d/dr05\n"
        "- Curved artifacts (proxy ω/k = c0 + βk²): dr01/dr03/dr04d/dr05\n\n"
        "OV-04x result (robustness-only)\n\n"
        "Computed with `formal/python/toe/observables/ov04_fit_family_robustness_lowk_ds02.py` under "
        f"`{str(adequacy_policy)}` with q_threshold={float(q_threshold):.12g}: \n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Report fingerprint: `{rep.fingerprint()}`\n"
    )


def write_ov04x_lock(
    *,
    lock_path: Path | None = None,
    adequacy_policy: str = "DQ-01_v1",
    q_threshold: float = 0.90,
    config_tag: str | None = None,
) -> Path:
    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    is_canonical = (str(adequacy_policy) == "DQ-01_v1") and (abs(float(q_threshold) - 0.90) <= 1e-12) and (config_tag is None)

    if out is None and is_canonical:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-04x_fit_family_robustness_DS02_lowk.md"
        )

    if out is None and (not is_canonical):
        raise ValueError("Non-canonical OV-04x lock requires explicit lock_path")

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        render_ov04x_lock_markdown(
            repo_root=repo_root,
            adequacy_policy=str(adequacy_policy),
            q_threshold=float(q_threshold),
            config_tag=config_tag,
        ),
        encoding="utf-8",
    )
    return out
