"""DS-02 units/scale ingestion invariant (diagnostic-only).

Goal
- Detect unit/scale/mapping defects that would make omega/k not be in m/s.
- Emit a deterministic artifact (no policy changes; no fit-family claims).

This is intentionally conservative and triage-focused: it compares candidate
unit assumptions against the B1 curved-fit c0 scale already present in frozen
artifacts, avoiding any external physical constants.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import hashlib
import json
import math
from pathlib import Path
from typing import Any

from formal.python.toe.observables.ovdq01_dq01_diagnostics_record import _find_repo_root


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _quantile_nearest_rank(xs: list[float], q: float) -> float:
    if not xs:
        raise ValueError("empty list")
    if q <= 0.0:
        return float(min(xs))
    if q >= 1.0:
        return float(max(xs))
    ys = sorted(float(x) for x in xs)
    idx = int(round(q * (len(ys) - 1)))
    return float(ys[idx])


def _median(xs: list[float]) -> float:
    return _quantile_nearest_rank(xs, 0.5)


def _iqr(xs: list[float]) -> float:
    return float(_quantile_nearest_rank(xs, 0.75) - _quantile_nearest_rank(xs, 0.25))


def _read_ds02_csv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        fieldnames = list(reader.fieldnames or [])
        rows = [dict(r) for r in reader]
    return fieldnames, rows


def _float_or_none(s: str | None) -> float | None:
    if s is None:
        return None
    t = str(s).strip()
    if t == "":
        return None
    return float(t)


def _load_b1_c0_scale(repo_root: Path) -> float:
    p = repo_root / "formal" / "external_evidence" / "bec_bragg_b1_second_dataset_TBD" / "dr01_fit_artifact_curved.json"
    d = json.loads(p.read_text(encoding="utf-8"))
    return float(d["c0"])


def _summarize_y(y: list[float]) -> dict[str, float]:
    return {
        "n": float(len(y)),
        "median": float(_median(y)),
        "iqr": float(_iqr(y)),
        "max": float(max(y)),
        "min": float(min(y)),
    }


def _log10_distance(a: float, b: float) -> float:
    if a <= 0.0 or b <= 0.0:
        return float("inf")
    return float(abs(math.log10(a / b)))


def _candidate_label(*, k_assumption: str, f_assumption: str, omega_assumption: str) -> str:
    return f"k:{k_assumption}; f:{f_assumption}; omega:{omega_assumption}"


@dataclass(frozen=True)
class OVDQ01DS02UnitsInvariantRecord:
    schema: str
    ds02_csv_relpath: str
    dr01_kmax_um_inv: float
    b1_c0_scale_m_per_s: float
    columns: list[str]
    n_rows: int
    sample_rows: list[dict[str, Any]]
    candidates: list[dict[str, Any]]
    best_candidate: dict[str, Any]
    verdict: dict[str, Any]
    suspicion_flags: list[str]
    notes: str

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return {
            "schema": str(self.schema),
            "ds02_csv_relpath": str(self.ds02_csv_relpath),
            "dr01_kmax_um_inv": float(self.dr01_kmax_um_inv),
            "b1_c0_scale_m_per_s": float(self.b1_c0_scale_m_per_s),
            "columns": list(self.columns),
            "n_rows": int(self.n_rows),
            "sample_rows": self.sample_rows,
            "candidates": self.candidates,
            "best_candidate": self.best_candidate,
            "verdict": self.verdict,
            "suspicion_flags": list(self.suspicion_flags),
            "notes": str(self.notes),
        }

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        payload = self.to_jsonable_without_fingerprint()
        payload["fingerprint"] = self.fingerprint()
        return payload


def ovdq01_ds02_units_invariant_record(*, dr01_kmax_um_inv: float = 3.33842) -> OVDQ01DS02UnitsInvariantRecord:
    repo_root = _find_repo_root(Path(__file__))
    csv_rel = "formal/external_evidence/bec_bragg_ds02_lowk_dataset_TBD/omega_k_data.csv"
    csv_path = repo_root / csv_rel

    columns, rows = _read_ds02_csv(csv_path)
    if len(rows) == 0:
        raise RuntimeError("DS-02 CSV has no rows")

    if "k_um_inv" not in columns or "omega_over_2pi_kHz" not in columns:
        raise RuntimeError("DS-02 CSV missing required columns: k_um_inv and omega_over_2pi_kHz")

    k_raw: list[float] = []
    f_over_2pi_khz: list[float] = []
    for r in rows:
        k = _float_or_none(r.get("k_um_inv"))
        f = _float_or_none(r.get("omega_over_2pi_kHz"))
        if k is None or f is None:
            continue
        if float(k) <= float(dr01_kmax_um_inv):
            k_raw.append(float(k))
            f_over_2pi_khz.append(float(f))

    if len(k_raw) < 5:
        raise RuntimeError("Insufficient DS-02 rows in DR01 window for invariant check")

    b1_c0 = _load_b1_c0_scale(repo_root)

    candidates: list[dict[str, Any]] = []

    def eval_candidate(*, k_scale: float, f_scale: float, omega_scale: float, label: str) -> dict[str, Any]:
        y: list[float] = []
        for (k, f_khz) in zip(k_raw, f_over_2pi_khz):
            k_si = float(k) * float(k_scale)
            f_hz = float(f_khz) * float(f_scale)
            omega = float(2.0 * math.pi) * float(f_hz) * float(omega_scale)
            if k_si == 0.0:
                continue
            y.append(float(omega / k_si))
        if len(y) == 0:
            raise RuntimeError("Candidate produced no y samples")
        s = _summarize_y(y)
        dist = _log10_distance(float(s["median"]), float(b1_c0))
        return {
            "label": str(label),
            "assumptions": {
                "k_scale_to_m_inv": float(k_scale),
                "f_scale_to_hz": float(f_scale),
                "omega_extra_scale": float(omega_scale),
            },
            "y_omega_over_k_m_per_s": s,
            "log10_distance_to_b1_c0_median": float(dist),
        }

    k_cases = [
        (1.0e6, "k_um_inv_to_m_inv"),
        (1.0, "k_already_m_inv"),
    ]
    # Per DS-02 provenance notes, the omega_over_2pi column is interpreted as Hz
    # (the column name contains 'kHz' for schema stability only). We still
    # evaluate a kHz hypothesis for auditability.
    f_cases = [
        (1.0, "omega_over_2pi_column_as_Hz"),
        (1.0e3, "omega_over_2pi_column_as_kHz"),
    ]
    omega_cases = [
        (1.0, "omega_equals_2pi_f"),
        (2.0 * math.pi, "double_2pi_probe"),
    ]

    for (k_scale, k_lab) in k_cases:
        for (f_scale, f_lab) in f_cases:
            for (om_scale, om_lab) in omega_cases:
                label = _candidate_label(k_assumption=k_lab, f_assumption=f_lab, omega_assumption=om_lab)
                candidates.append(eval_candidate(k_scale=k_scale, f_scale=f_scale, omega_scale=om_scale, label=label))

    # Select best candidate under the **Hz interpretation** (per provenance).
    hz_candidates = [c for c in candidates if float(c["assumptions"]["f_scale_to_hz"]) == 1.0]
    if not hz_candidates:
        raise RuntimeError("Invariant: expected at least one Hz candidate")
    best = min(hz_candidates, key=lambda c: float(c["log10_distance_to_b1_c0_median"]))

    reason_codes: list[str] = []
    # This is a triage invariant, not a policy gate: we allow a wide band here
    # to reduce false negatives across regime-separated datasets.
    passes = bool(float(best["log10_distance_to_b1_c0_median"]) <= 3.0)
    if not passes:
        reason_codes.append("hz_interpretation_not_within_factor_1000_of_b1_c0")

    flags: list[str] = []
    k_scale = float(best["assumptions"]["k_scale_to_m_inv"])
    f_scale = float(best["assumptions"]["f_scale_to_hz"])
    om_scale = float(best["assumptions"]["omega_extra_scale"])

    if k_scale == 1.0e6:
        flags.append("k_units_mismatch_suspected")
    if om_scale != 1.0:
        flags.append("double_2pi_suspected")

    sample_rows: list[dict[str, Any]] = []
    for r in rows[:5]:
        sample_rows.append(
            {
                "k_um_inv": _float_or_none(r.get("k_um_inv")),
                "omega_over_2pi_kHz": _float_or_none(r.get("omega_over_2pi_kHz")),
                "source": r.get("source"),
                "figure": r.get("figure"),
                "notes": r.get("notes"),
            }
        )

    verdict = {
        "passes": bool(passes),
        "reason_codes": reason_codes,
        "rule": "hz_interpretation_best_candidate_within_factor_1000_of_b1_c0_scale",
    }

    return OVDQ01DS02UnitsInvariantRecord(
        schema="OV-DQ-01_DS02_units_invariant/v1",
        ds02_csv_relpath=csv_rel,
        dr01_kmax_um_inv=float(dr01_kmax_um_inv),
        b1_c0_scale_m_per_s=float(b1_c0),
        columns=columns,
        n_rows=int(len(rows)),
        sample_rows=sample_rows,
        candidates=candidates,
        best_candidate=best,
        verdict=verdict,
        suspicion_flags=flags,
        notes=(
            "Diagnostic-only invariant check: evaluates candidate unit assumptions for DS-02 and compares implied omega/k scale "
            "to the B1 curved-fit c0 scale already present in frozen artifacts. The DS-02 omega_over_2pi column is interpreted as Hz "
            "per provenance; a kHz hypothesis is evaluated for auditability only. No policy changes; no physics claim."
        ),
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-DQ-01" / "DS02_units_invariant.json"


def write_ds02_units_invariant_artifact(*, path: Path | None = None) -> Path:
    out = default_artifact_path() if path is None else Path(path)
    rec = ovdq01_ds02_units_invariant_record()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(rec.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8")
    return out
