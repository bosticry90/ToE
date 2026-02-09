"""OV-DQ-01: policy sensitivity diagnostic (q_threshold grid).

Purpose
- Provide a pinned, deterministic "what-if" summary of the OV-01g family
    selection decision under a small grid of q_threshold values.
- This is *diagnostic only*: it does not mutate DQ-01_v1 thresholds or the
  canonical q_threshold used in any gate.

This record answers: if q_threshold were X (holding all other logic fixed),
would the policy prefer the curved family, and which clause(s) would block it?

Notes
- For OV-03x and OV-04x, q_ratio/curved_adequacy_passes are loaded from the
    canonical robustness locks.
- For OV-01g, the robustness report is recomputed deterministically from the
    already-frozen external-evidence fit artifacts (Steinhauer 2001).
- For OV-02x, the metamorphic invariance gate is recomputed per q_threshold
    (it wraps OV-01g, so its outcome can depend on q_threshold).
- Failure reasons are computed deterministically using the same clause logic,
  but evaluated against each candidate q_threshold.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math
from pathlib import Path
from typing import Any

from formal.python.toe.constraints.fn01_artifact import fn01_make_P_cubic_artifact
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.dr01_fit_quality import DR01FitQualityCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import ov01_fit_family_robustness_gate
from formal.python.toe.observables.ov02_digitization_invariance import ov02_digitization_invariance_gate
from formal.python.toe.observables.ovdq01_dq01_diagnostics_record import _find_repo_root, _load_robustness_report_from_lock


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-DQ-01" / "OV-DQ-01_policy_sensitivity.json"


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_sample_kw_from_fit_json(path: Path) -> tuple[tuple[float, float], ...]:
    d = _load_json(path)
    if d.get("sample_kw") is None:
        raise ValueError(f"Missing sample_kw in {path.as_posix()}")
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


def _what_if_reasons(*, r_max_linear: float, curved_adequacy_passes: bool, q_ratio: float, q_threshold: float) -> list[str]:
    reasons: list[str] = []

    if float(r_max_linear) == 0.0:
        reasons.append("r_max_linear_zero")

    if not bool(curved_adequacy_passes):
        reasons.append("curved_adequacy_failed")

    if (not math.isnan(float(q_ratio))) and (float(q_ratio) > float(q_threshold)):
        reasons.append("q_ratio_above_threshold")

    would_prefer = bool(curved_adequacy_passes and (not math.isnan(float(q_ratio))) and (float(q_ratio) <= float(q_threshold)))
    if (not would_prefer) and (not reasons):
        reasons.append("policy_non_prefer")

    return reasons


def _evaluate_grid(*, obs_id: str, lock_rel_path: str, thresholds: list[float]) -> dict[str, Any]:
    repo_root = _find_repo_root(Path(__file__))
    rep, fp = _load_robustness_report_from_lock(repo_root=repo_root, lock_rel_path=lock_rel_path)

    out_rows: list[dict[str, Any]] = []
    for t in thresholds:
        reasons = _what_if_reasons(
            r_max_linear=float(rep.r_max_linear),
            curved_adequacy_passes=bool(rep.curved_adequacy_passes),
            q_ratio=float(rep.q_ratio),
            q_threshold=float(t),
        )
        would_prefer = bool(bool(rep.curved_adequacy_passes) and (not math.isnan(float(rep.q_ratio))) and (float(rep.q_ratio) <= float(t)))
        out_rows.append(
            {
                "q_threshold": float(t),
                "would_prefer_curved": bool(would_prefer),
                "robustness_failed": bool(not would_prefer),
                "blocking_reasons": reasons,
            }
        )

    return {
        "observable_id": str(obs_id),
        "robustness_lock_relpath": str(lock_rel_path),
        "robustness_report_fingerprint": str(fp),
        "q_ratio_locked": float(rep.q_ratio),
        "q_threshold_locked": float(rep.q_threshold),
        "curved_adequacy_passes_locked": bool(rep.curved_adequacy_passes),
        "prefer_curved_locked": bool(rep.prefer_curved),
        "grid": out_rows,
    }


def _evaluate_grid_from_ov01g_external_evidence(*, thresholds: list[float]) -> dict[str, Any]:
    repo_root = _find_repo_root(Path(__file__))
    base = repo_root / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

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

    out_rows: list[dict[str, Any]] = []
    for t in thresholds:
        reasons = _what_if_reasons(
            r_max_linear=float(rep.r_max_linear),
            curved_adequacy_passes=bool(rep.curved_adequacy_passes),
            q_ratio=float(rep.q_ratio),
            q_threshold=float(t),
        )
        would_prefer = bool(bool(rep.curved_adequacy_passes) and (not math.isnan(float(rep.q_ratio))) and (float(rep.q_ratio) <= float(t)))
        out_rows.append(
            {
                "q_threshold": float(t),
                "would_prefer_curved": bool(would_prefer),
                "robustness_failed": bool(not would_prefer),
                "blocking_reasons": reasons,
            }
        )

    return {
        "observable_id": "OV-01g",
        "robustness_source": "external_evidence_frozen_fit_artifacts",
        "external_evidence_relpath": "formal/external_evidence/bec_bragg_steinhauer_2001",
        "robustness_report_fingerprint": str(rep.fingerprint()),
        "q_ratio_locked": float(rep.q_ratio),
        "q_threshold_locked": float(rep.q_threshold),
        "curved_adequacy_passes_locked": bool(rep.curved_adequacy_passes),
        "prefer_curved_locked": bool(rep.prefer_curved),
        "grid": out_rows,
    }


def _evaluate_grid_for_ov02x(*, thresholds: list[float]) -> dict[str, Any]:
    repo_root = _find_repo_root(Path(__file__))
    base = repo_root / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    # Use the same 4-window set used by OV-01g mainline (DR-02a/03a/04d/05a).
    s02 = _load_sample_kw_from_fit_json(base / "dr01_fit_artifact.json")
    s03 = _load_sample_kw_from_fit_json(base / "dr03_fit_artifact.json")
    s04d = _load_sample_kw_from_fit_json(base / "dr04d_fit_artifact.json")
    s05 = _load_sample_kw_from_fit_json(base / "dr05_fit_artifact.json")

    fn = fn01_make_P_cubic_artifact(g=0.3)

    out_rows: list[dict[str, Any]] = []
    locked_row: dict[str, Any] | None = None

    for t in thresholds:
        rep = ov02_digitization_invariance_gate(
            fn,
            windows_sample_kw=[s02, s03, s04d, s05],
            rel_eps=0.01,
            patterns=("baseline", "alt_pm", "ramp"),
            q_threshold=float(t),
            adequacy_policy="DQ-01_v1",
        )
        reasons: list[str] = []
        if bool(rep.robustness_failed):
            reasons.append("digitization_invariance_failed")

        row = {
            "q_threshold": float(t),
            "baseline_prefer_curved": bool(rep.baseline_prefer_curved),
            "all_scenarios_match_baseline": bool(rep.all_scenarios_match_baseline),
            "robustness_failed": bool(rep.robustness_failed),
            "blocking_reasons": reasons,
            "report_fingerprint": str(rep.fingerprint()),
        }
        out_rows.append(row)

        if abs(float(t) - 0.90) <= 1e-12:
            locked_row = dict(row)

    if locked_row is None:
        raise ValueError("q_threshold_grid must include 0.90 for OV-02x locked-point reporting")

    return {
        "observable_id": "OV-02x",
        "robustness_source": "metamorphic_gate_recomputed",
        "external_evidence_relpath": "formal/external_evidence/bec_bragg_steinhauer_2001",
        "q_threshold_locked": float(0.90),
        "baseline_prefer_curved_locked": bool(locked_row["baseline_prefer_curved"]),
        "robustness_failed_locked": bool(locked_row["robustness_failed"]),
        "locked_report_fingerprint": str(locked_row["report_fingerprint"]),
        "grid": out_rows,
    }


@dataclass(frozen=True)
class OVDQ01PolicySensitivityRecord:
    schema: str
    notes: str
    q_threshold_grid: list[float]
    ov01g: dict[str, Any]
    ov02x: dict[str, Any]
    ov04x: dict[str, Any]
    ov03x: dict[str, Any]

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "notes": str(self.notes),
            "q_threshold_grid": [float(x) for x in self.q_threshold_grid],
            "ov01g": self.ov01g,
            "ov02x": self.ov02x,
            "ov04x": self.ov04x,
            "ov03x": self.ov03x,
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = self.to_jsonable_without_fingerprint()
        d["fingerprint"] = self.fingerprint()
        return d


def ovdq01_policy_sensitivity_record(*, q_threshold_grid: list[float] | None = None) -> OVDQ01PolicySensitivityRecord:
    grid = [0.85, 0.90, 0.95, 1.00, 1.05, 1.10, 1.15] if q_threshold_grid is None else [float(x) for x in q_threshold_grid]

    ov01g = _evaluate_grid_from_ov01g_external_evidence(thresholds=grid)
    ov02x = _evaluate_grid_for_ov02x(thresholds=grid)

    ov04x = _evaluate_grid(
        obs_id="OV-04x",
        lock_rel_path="formal/markdown/locks/observables/OV-04x_fit_family_robustness_DS02_lowk.md",
        thresholds=grid,
    )
    ov03x = _evaluate_grid(
        obs_id="OV-03x",
        lock_rel_path="formal/markdown/locks/observables/OV-03x_fit_family_robustness_B1_dataset.md",
        thresholds=grid,
    )

    return OVDQ01PolicySensitivityRecord(
        schema="OV-DQ-01_policy_sensitivity/v2",
        notes=(
            "Diagnostic-only policy sensitivity summary for the OV-01g family-selection logic under a q_threshold grid. "
            "Does not change DQ-01_v1 thresholds or canonical q_threshold; records what would happen under alternate q_threshold values."
        ),
        q_threshold_grid=grid,
        ov01g=ov01g,
        ov02x=ov02x,
        ov04x=ov04x,
        ov03x=ov03x,
    )


def write_ovdq01_policy_sensitivity_artifact(*, path: Path | None = None) -> Path:
    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    rec = ovdq01_policy_sensitivity_record().to_jsonable()
    out.write_text(json.dumps(rec, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
