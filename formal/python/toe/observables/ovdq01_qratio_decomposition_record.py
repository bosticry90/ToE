"""OV-DQ-01: q_ratio decomposition diagnostic (Case B support).

Goal
- Explain *what drives* q_ratio = R_max_curved / R_max_linear for OV-04x and OV-03x.
- Provide deterministic, audit-friendly decomposition of the underlying
  multi-window residual structure (pairwise residuals + window contributions).

Scope / limits
- Bookkeeping/diagnostic only; no policy mutation; no physics claim.
- Does not change DQ-01 thresholds or q_threshold.

Definition (as implemented by OV-01g)
- For each fit family (linear, curved), compute OV-01 observable values across
  the window set, then pairwise residuals:
    R_ij = |obs_i - obs_j| / max(|obs_i|, |obs_j|, epsilon)
- R_max is the maximum of R_ij over all i<j.
- q_ratio = R_max_curved / R_max_linear.

This record decomposes each family into:
- The full pairwise residual list, with tags.
- The R_max-dominant pair.
- Per-window contributions defined as max residual involving that window.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import _dedupe_aligned_windows
from formal.python.toe.observables.ov01_multi_fit_stability import ov01_multi_fit_stability
from formal.python.toe.observables.ov01_multi_fit_stability_curved import ov01_multi_fit_stability_curved
from formal.python.toe.observables.ov01_observable import ov01_observable_residual_from
from formal.python.toe.observables.ov01_observable_curved import ov01_observable_residual_from_curved
from formal.python.toe.observables.ovdq01_dq01_diagnostics_record import _find_repo_root, _load_robustness_report_from_lock


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-DQ-01" / "OV-DQ-01_qratio_decomposition.json"


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


def _pairwise_decomposition(*, tags: list[str], pairwise_r: list[tuple[int, int, float]]) -> dict[str, Any]:
    if not tags:
        raise ValueError("empty tags")

    pairs = [
        {"i": int(i), "j": int(j), "r": float(r), "tag_i": str(tags[i]), "tag_j": str(tags[j])}
        for (i, j, r) in pairwise_r
    ]

    # r_max pair
    i_max, j_max, r_max = max(pairwise_r, key=lambda t: float(t[2]))
    r_max_pair = {
        "i": int(i_max),
        "j": int(j_max),
        "r": float(r_max),
        "tag_i": str(tags[int(i_max)]),
        "tag_j": str(tags[int(j_max)]),
    }

    # per-window contribution: max r involving that window
    contrib: list[dict[str, Any]] = []
    for idx in range(len(tags)):
        r_vals = [float(r) for (i, j, r) in pairwise_r if (int(i) == idx or int(j) == idx)]
        r_i = float(max(r_vals)) if r_vals else 0.0
        contrib.append({"idx": int(idx), "tag": str(tags[idx]), "max_pairwise_r": float(r_i)})

    sum_contrib = float(sum(float(c["max_pairwise_r"]) for c in contrib))
    for c in contrib:
        share = 0.0 if sum_contrib == 0.0 else float(c["max_pairwise_r"]) / sum_contrib
        c["share_of_sum_max_pairwise_r"] = float(share)

    dominant = max(contrib, key=lambda c: float(c["max_pairwise_r"]))

    pairs_sorted = sorted(pairs, key=lambda p: float(p["r"]), reverse=True)

    top_k = 5
    return {
        "n_windows": int(len(tags)),
        "pairwise_r": pairs,
        "r_max_pair": r_max_pair,
        "window_contributions": contrib,
        "dominant_window_by_max_pairwise_r": dominant,
        "top_pairs_by_r": pairs_sorted[:top_k],
        "sum_window_max_pairwise_r": float(sum_contrib),
        "dominance_share": float(dominant.get("share_of_sum_max_pairwise_r", 0.0)),
    }


@dataclass(frozen=True)
class OVDQ01QRatioDecompositionRecord:
    schema: str
    notes: str
    ov04x: dict[str, Any]
    ov03x: dict[str, Any]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "notes": str(self.notes),
            "ov04x": self.ov04x,
            "ov03x": self.ov03x,
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def _compute_for_observable(*, repo_root: Path, obs_id: str) -> dict[str, Any]:
    if obs_id == "OV-04x":
        ev_dir = repo_root / "formal" / "external_evidence" / "bec_bragg_ds02_lowk_dataset_TBD"
        lock_rel = "formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md"
    elif obs_id == "OV-03x":
        ev_dir = repo_root / "formal" / "external_evidence" / "bec_bragg_b1_second_dataset_TBD"
        lock_rel = "formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md"
    else:
        raise ValueError(f"Unsupported obs_id: {obs_id!r}")

    lin_paths = [
        ev_dir / "dr01_fit_artifact.json",
        ev_dir / "dr03_fit_artifact.json",
        ev_dir / "dr04d_fit_artifact.json",
        ev_dir / "dr05_fit_artifact.json",
    ]
    curv_paths = [
        ev_dir / "dr01_fit_artifact_curved.json",
        ev_dir / "dr03_fit_artifact_curved.json",
        ev_dir / "dr04d_fit_artifact_curved.json",
        ev_dir / "dr05_fit_artifact_curved.json",
    ]

    dr_lin = [_load_dr01_fit_from_json(p) for p in lin_paths]
    dr_curv = [_load_dr01_fit_curved_from_json(p) for p in curv_paths]

    dr_lin_dedup, dr_curv_dedup = _dedupe_aligned_windows(dr_lin, dr_curv)

    fn = fn01_make_P_cubic_artifact(g=0.3)

    rep_lin = ov01_multi_fit_stability(fn, dr_lin_dedup, config_tag=f"{obs_id}_linear_family_envelope")
    rep_curv = ov01_multi_fit_stability_curved(fn, dr_curv_dedup, config_tag=f"{obs_id}_curved_family_envelope")

    # Recompute observable reports to attach stable tags.
    lin_obs_reps = [ov01_observable_residual_from(fn, dr) for dr in dr_lin_dedup]
    curv_obs_reps = [ov01_observable_residual_from_curved(fn, dr) for dr in dr_curv_dedup]

    lin_tags = [str(dr.tag) for dr in dr_lin_dedup]
    curv_tags = [str(dr.tag) for dr in dr_curv_dedup]

    lin_windows = [
        {
            "idx": int(i),
            "tag": str(dr.tag),
            "data_fingerprint": dr.data_fingerprint,
            "dr_fingerprint": str(dr.fingerprint()),
            "obs_value": float(r.obs_value),
            "metric_fingerprint": str(r.metric_fingerprint),
        }
        for i, (dr, r) in enumerate(zip(dr_lin_dedup, lin_obs_reps, strict=True))
    ]

    curv_windows = [
        {
            "idx": int(i),
            "tag": str(dr.tag),
            "data_fingerprint": dr.data_fingerprint,
            "dr_fingerprint": str(dr.fingerprint()),
            "obs_value": float(r.obs_value),
            "metric_fingerprint": str(r.metric_fingerprint),
        }
        for i, (dr, r) in enumerate(zip(dr_curv_dedup, curv_obs_reps, strict=True))
    ]

    # Load the locked robustness report for cross-check.
    locked_report, locked_fp = _load_robustness_report_from_lock(repo_root=repo_root, lock_rel_path=lock_rel)

    linear_decomp = _pairwise_decomposition(tags=lin_tags, pairwise_r=list(rep_lin.pairwise_r))
    curved_decomp = _pairwise_decomposition(tags=curv_tags, pairwise_r=list(rep_curv.pairwise_r))

    r_max_linear = float(rep_lin.r_max)
    r_max_curved = float(rep_curv.r_max)
    q_ratio = float("nan") if r_max_linear == 0.0 else float(r_max_curved / r_max_linear)

    # Outlier flag: one window dominates the share-of-sum(max_pairwise_r) heuristic.
    outlier = bool(float(curved_decomp["dominance_share"]) > 0.5)

    return {
        "observable_id": str(obs_id),
        "robustness_lock_relpath": str(lock_rel),
        "robustness_report_fingerprint": str(locked_fp),
        "robustness_q_ratio_locked": float(locked_report.q_ratio),
        "robustness_q_threshold_locked": float(locked_report.q_threshold),
        "q_ratio_recomputed": float(q_ratio),
        "r_max_linear_recomputed": float(r_max_linear),
        "r_max_curved_recomputed": float(r_max_curved),
        "linear": {
            "windows": lin_windows,
            "decomposition": linear_decomp,
        },
        "curved": {
            "windows": curv_windows,
            "decomposition": curved_decomp,
        },
        "flags": {
            "qratio_outlier_window_dominates_curved": bool(outlier),
        },
    }


def ovdq01_qratio_decomposition_record() -> OVDQ01QRatioDecompositionRecord:
    repo_root = _find_repo_root(Path(__file__))

    ov04x = _compute_for_observable(repo_root=repo_root, obs_id="OV-04x")
    ov03x = _compute_for_observable(repo_root=repo_root, obs_id="OV-03x")

    return OVDQ01QRatioDecompositionRecord(
        schema="OV-DQ-01_qratio_decomposition/v1",
        notes=(
            "Diagnostic-only decomposition of q_ratio = R_max_curved/R_max_linear for OV-04x and OV-03x, "
            "including pairwise residual structure and per-window max-pairwise residual contributions. "
            "No policy change; no physics claim."
        ),
        ov04x=ov04x,
        ov03x=ov03x,
    )


def write_ovdq01_qratio_decomposition_artifact(*, path: Path | None = None) -> Path:
    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    rec = ovdq01_qratio_decomposition_record().to_jsonable()
    out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
