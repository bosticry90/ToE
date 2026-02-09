"""OV-BR-01: regime bridge declaration + record (pure bookkeeping).

Purpose
- Declare two k-bands ("split into sub-bands") anchored by OV-01g (low-k) and
  OV-03x (high-k), and compute only band geometry: overlap / gap.
- Record regime-separated preference outcomes as already-evaluated elsewhere.

Scope / limits
- split into sub-bands
- evaluated separately
- no averaging across regimes
- no continuity claim
- β not inferred / β-null posture

Design constraints
- Deterministic (no RNG).
- No fitting. No model selection. No statistics.
- Prefer canonical band sources: reuse OV-XD-03 band semantics.

Notes
- This record is a controlled “continuity bridge” without asserting continuity.
  It records separately measured preferences + band geometry only.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re
from pathlib import Path
from typing import Any

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import ov01_fit_family_robustness_gate
from formal.python.toe.observables.ov03_fit_family_robustness import ov03_fit_family_robustness_gate
from formal.python.toe.observables.ovxd03_overlap_band_record import ovxd03_overlap_band_record


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


def _extract_json_block(md_text: str) -> dict[str, Any]:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise ValueError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_report_fingerprint(md_text: str) -> str:
    m = re.search(r"Report fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise ValueError("Missing report fingerprint line")
    return m.group(1)


def _load_json(path: Path) -> dict[str, Any]:
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


@dataclass(frozen=True)
class OVBR01RegimeBridgeRecord:
    schema: str

    low_band: tuple[float, float]
    high_band: tuple[float, float]

    overlap: tuple[float, float] | None
    gap: tuple[float, float] | None
    gap_width: float | None

    low_preference: dict[str, Any]
    high_preference: dict[str, Any]

    comparability_statement: str

    provenance: dict[str, Any]
    notes: str

    def to_jsonable(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "low_band": [float(self.low_band[0]), float(self.low_band[1])],
            "high_band": [float(self.high_band[0]), float(self.high_band[1])],
            "overlap": None if self.overlap is None else [float(self.overlap[0]), float(self.overlap[1])],
            "gap": None if self.gap is None else [float(self.gap[0]), float(self.gap[1])],
            "gap_width": None if self.gap_width is None else float(self.gap_width),
            "low_preference": dict(self.low_preference),
            "high_preference": dict(self.high_preference),
            "comparability_statement": str(self.comparability_statement),
            "provenance": self.provenance,
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable())


def _compute_overlap_and_gap(
    *, low_band: tuple[float, float], high_band: tuple[float, float]
) -> tuple[tuple[float, float] | None, tuple[float, float] | None, float | None]:
    low_min, low_max = float(low_band[0]), float(low_band[1])
    high_min, high_max = float(high_band[0]), float(high_band[1])

    ov_min = max(low_min, high_min)
    ov_max = min(low_max, high_max)

    if ov_max >= ov_min:
        return (float(ov_min), float(ov_max)), None, None

    # Disjoint: record ordered gap [kmax_low, kmin_high] in ascending order.
    a = min(low_max, high_max)
    b = max(low_min, high_min)
    gap = (float(a), float(b))
    return None, gap, float(gap[1] - gap[0])


def _compute_ov01g_preference(*, repo_root: Path) -> dict[str, Any]:
    base = repo_root / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    # Canonical 4-window set for OV-01g mainline uses DR-04d (N>=5).
    lin_paths = [
        base / "dr01_fit_artifact.json",
        base / "dr03_fit_artifact.json",
        base / "dr04d_fit_artifact.json",
        base / "dr05_fit_artifact.json",
    ]
    curv_paths = [
        base / "dr01_fit_artifact_curved.json",
        base / "dr03_fit_artifact_curved.json",
        base / "dr04d_fit_artifact_curved.json",
        base / "dr05_fit_artifact_curved.json",
    ]

    dr_lin = [_load_dr01_fit_from_json(p) for p in lin_paths]
    dr_curv = [_load_dr01_fit_curved_from_json(p) for p in curv_paths]

    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep = ov01_fit_family_robustness_gate(
        fn,
        dr_lin,
        dr_curv,
        adequacy_policy="DQ-01_v1",
    )

    return {
        "observable_id": "OV-01g",
        "adequacy_policy": rep.adequacy_policy,
        "prefer_curved": bool(rep.prefer_curved),
        "robustness_failed": bool(rep.robustness_failed),
        "report_fingerprint": rep.fingerprint(),
    }


def _load_ov03x_preference_from_lock(*, repo_root: Path) -> dict[str, Any]:
    lock_path = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-03x_fit_family_robustness_B1_dataset.md"
    )

    text = lock_path.read_text(encoding="utf-8")
    payload = _extract_json_block(text)
    report_fp = _extract_report_fingerprint(text)

    # Defensive: prefer the fingerprint line (it is the locked report fingerprint).
    if payload.get("config_tag") is None:
        raise ValueError("OV-03x lock JSON missing config_tag")

    return {
        "observable_id": "OV-03x",
        "adequacy_policy": str(payload.get("adequacy_policy", "unknown")),
        "prefer_curved": bool(payload["prefer_curved"]),
        "robustness_failed": bool(payload["robustness_failed"]),
        "report_fingerprint": str(report_fp),
        "lock_payload_fingerprint": _sha256_json(payload),
    }


def ovbr01_regime_bridge_record() -> OVBR01RegimeBridgeRecord:
    """Compute the OV-BR-01 bookkeeping record (no fitting / no inference)."""

    repo_root = _find_repo_root(Path(__file__))

    xd03 = ovxd03_overlap_band_record()
    bands = xd03.bands

    low_band = (float(bands["OV-01g"].k_min), float(bands["OV-01g"].k_max))
    high_band = (float(bands["OV-03x"].k_min), float(bands["OV-03x"].k_max))

    overlap, gap, gap_width = _compute_overlap_and_gap(low_band=low_band, high_band=high_band)

    low_pref = _compute_ov01g_preference(repo_root=repo_root)
    high_pref = _load_ov03x_preference_from_lock(repo_root=repo_root)

    if overlap is not None:
        comparability_statement = (
            "Overlap exists; comparison is meaningful only within the overlap band. "
            "This record does not assert continuity; it records regime-separated results and band geometry only. "
            "No averaging across regimes."
        )
    else:
        comparability_statement = (
            "No overlap; comparison is not valid. "
            "This record does not assert continuity; it records regime-separated results and band geometry only. "
            "No averaging across regimes."
        )

    provenance: dict[str, Any] = {
        "bands": {
            "source": "OV-XD-03",
            "ovxd03_schema": xd03.schema,
            "ovxd03_fingerprint": xd03.fingerprint(),
            "ovxd03_provenance": xd03.to_jsonable().get("provenance", {}),
        },
        "preferences": {
            "low": {
                "source": "computed",
                "module": "formal/python/toe/observables/ov01_fit_family_robustness.py",
                "note": "Evaluated separately (no averaging across regimes); β not inferred / β-null posture.",
            },
            "high": {
                "source": "lock",
                "lock_path": "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
                "note": "Evaluated separately (no averaging across regimes); β not inferred / β-null posture.",
            },
        },
    }

    return OVBR01RegimeBridgeRecord(
        schema="OV-BR-01/v1",
        low_band=low_band,
        high_band=high_band,
        overlap=overlap,
        gap=gap,
        gap_width=gap_width,
        low_preference=low_pref,
        high_preference=high_pref,
        comparability_statement=comparability_statement,
        provenance=provenance,
        notes=(
            "Bookkeeping only; split into sub-bands; evaluated separately; no averaging across regimes; "
            "no continuity claim; β not inferred / β-null posture."
        ),
    )


def render_ovbr01_lock_markdown(record: OVBR01RegimeBridgeRecord) -> str:
    payload = record.to_jsonable()
    fp = record.fingerprint()

    scope_fence = (
        "This record does not assert continuity; it records regime-separated results and their k-band overlap/gap only. "
        "No averaging."
    )

    json_block = json.dumps(payload, indent=2, sort_keys=True)

    return (
        "# OV-BR-01 — Regime bridge record (computed)\n\n"
        f"{scope_fence}\n\n"
        "Scope / limits\n"
        "- split into sub-bands\n"
        "- evaluated separately\n"
        "- no averaging across regimes\n"
        "- no continuity claim\n"
        "- β not inferred / β-null posture\n\n"
        "Record (computed)\n\n"
        "```json\n"
        f"{json_block}\n"
        "```\n\n"
        f"Record fingerprint: `{fp}`\n"
    )


def write_ovbr01_lock(*, lock_path: Path | None = None) -> Path:
    """Write the OV-BR-01 lock markdown deterministically."""

    repo_root = _find_repo_root(Path(__file__))
    out = lock_path
    if out is None:
        out = (
            repo_root
            / "formal"
            / "markdown"
            / "locks"
            / "observables"
            / "OV-BR-01_regime_bridge_record.md"
        )

    rec = ovbr01_regime_bridge_record()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render_ovbr01_lock_markdown(rec), encoding="utf-8")
    return out
