"""OV-UCFF-07: Cross-metric coupling audit (bookkeeping only).

Purpose
- Quantify deterministic coupling between:
  - spectral entropy time series (normalized band-energy entropy in [0,1])
  - per-band spectral energy-fraction modulation (adjacent-frame changes)
  - optional adjacent-frame band-distribution drift (Jensen–Shannon divergence)

This is a numeric-only internal audit scaffold. It does not assert any UCFF
physical interpretation.

Method sketch
- For each frame x_t, compute rFFT power |FFT(x_t)|^2.
- Partition rFFT bins into n_bands contiguous bands.
- Convert band energies to a normalized distribution p_t.
- Compute normalized entropy H_t.
- Define per-time-step modulation m_t = mean_b |p_t[b] - p_{t-1}[b]|.
- Compute correlations:
  - corr(H_t, p_t[b]) per band
  - corr(ΔH_t, Δp_t[b]) per band
  - corr(H_t, m_t) (aligned)
  - corr(ΔH_t, m_t) (aligned)
  - lag scan corr(ΔH_t, m_{t+lag}) for lag in [-L..L]
- Optional drift series d_t = JS(p_{t-1}, p_t) and coupling corr(d_t, |ΔH_t|).
"""

from __future__ import annotations

from dataclasses import asdict
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np


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


def _as_2d_float(x: np.ndarray) -> np.ndarray:
    a = np.asarray(x, dtype=float)
    if a.ndim != 2:
        raise ValueError("X must be a 2D array of shape (n_frames, n_bins)")
    if a.shape[0] < 2:
        raise ValueError("need at least 2 frames")
    if a.shape[1] < 2:
        raise ValueError("need at least 2 bins")
    return a


def _band_edges(n_bins: int, n_bands: int) -> list[int]:
    if n_bands < 2:
        raise ValueError("n_bands must be >= 2")
    if n_bins < n_bands:
        raise ValueError("n_bands must be <= number of rFFT bins")

    edges = np.linspace(0, n_bins, n_bands + 1, dtype=int).tolist()
    for i in range(1, len(edges)):
        if edges[i] <= edges[i - 1]:
            edges[i] = edges[i - 1] + 1
    edges[-1] = n_bins
    return edges


def _spectral_power_rfft(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=float).ravel()
    F = np.fft.rfft(x)
    return np.abs(F) ** 2


def _entropy_normalized(p: np.ndarray, *, eps: float) -> float:
    p = np.asarray(p, dtype=float)
    p = p / (float(np.sum(p)) + float(eps))
    n = int(p.size)
    if n <= 1:
        return 0.0
    H = -float(np.sum(p * np.log(p + float(eps))))
    return float(H / np.log(float(n)))


def _pearson_corr(a: np.ndarray, b: np.ndarray, *, eps: float) -> float:
    a = np.asarray(a, dtype=float).ravel()
    b = np.asarray(b, dtype=float).ravel()
    if a.size != b.size:
        raise ValueError("corr inputs must have same length")
    if a.size < 2:
        return 0.0
    a0 = a - float(np.mean(a))
    b0 = b - float(np.mean(b))
    sa = float(np.sqrt(np.mean(a0 * a0)))
    sb = float(np.sqrt(np.mean(b0 * b0)))
    if sa < float(eps) or sb < float(eps):
        return 0.0
    return float(np.mean(a0 * b0) / (sa * sb))


def _js_divergence(p: np.ndarray, q: np.ndarray, *, eps: float) -> float:
    p = np.asarray(p, dtype=float)
    q = np.asarray(q, dtype=float)
    p = p / (float(np.sum(p)) + float(eps))
    q = q / (float(np.sum(q)) + float(eps))
    m = 0.5 * (p + q)

    def kl(a: np.ndarray, b: np.ndarray) -> float:
        return float(np.sum(a * (np.log(a + float(eps)) - np.log(b + float(eps)))))

    return 0.5 * kl(p, m) + 0.5 * kl(q, m)


def _lag_scan_corr(x: np.ndarray, y: np.ndarray, *, max_lag: int, eps: float) -> tuple[list[dict[str, float]], int, float]:
    """Compute corr(x_t, y_{t+lag}) for lag in [-max_lag..max_lag]."""
    x = np.asarray(x, dtype=float).ravel()
    y = np.asarray(y, dtype=float).ravel()
    if x.size != y.size:
        raise ValueError("lag scan inputs must have same length")
    n = int(x.size)
    max_lag = int(max(0, min(max_lag, n - 2)))

    rows: list[dict[str, float]] = []
    best_lag = 0
    best_abs = -1.0
    best_corr = 0.0

    for lag in range(-max_lag, max_lag + 1):
        if lag < 0:
            xs = x[-lag:]
            ys = y[: n + lag]
        elif lag > 0:
            xs = x[: n - lag]
            ys = y[lag:]
        else:
            xs = x
            ys = y
        c = _pearson_corr(xs, ys, eps=float(eps))
        rows.append({"lag": float(lag), "corr": float(c)})
        ac = abs(float(c))
        if ac > best_abs:
            best_abs = ac
            best_lag = int(lag)
            best_corr = float(c)

    return rows, best_lag, best_corr


@dataclass(frozen=True)
class OVUCFF07CrossMetricCouplingReport:
    schema: str
    config_tag: str
    eps: float
    n_frames: int
    n_bins: int
    n_fft_bins: int
    n_bands: int
    band_edges: list[int]
    dt: float
    max_lag: int

    entropy_norm_mean: float
    modulation_mean: float
    drift_js_mean: float

    per_band_corr_entropy_frac: list[float]
    per_band_corr_dentropy_dfrac: list[float]

    corr_entropy_modulation: float
    corr_dentropy_modulation: float
    lag_scan_dentropy_modulation: list[dict[str, float]]
    best_lag_dentropy_modulation: int
    best_corr_dentropy_modulation: float

    corr_abs_dentropy_drift_js: float

    series_entropy_norm: list[float] | None
    series_modulation_mean_abs_dfrac: list[float] | None
    series_drift_js: list[float] | None

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovucff07_cross_metric_coupling_audit(
    *,
    X: np.ndarray,
    n_bands: int = 8,
    dt: float = 1.0,
    eps: float = 1e-12,
    max_lag: int = 4,
    config_tag: str = "OV-UCFF-07_cross_metric_coupling_v1",
    include_series_limit: int = 256,
) -> OVUCFF07CrossMetricCouplingReport:
    X = _as_2d_float(X)
    if dt <= 0:
        raise ValueError("dt must be > 0")
    if eps <= 0:
        raise ValueError("eps must be > 0")

    n_frames, n_bins = int(X.shape[0]), int(X.shape[1])
    n_fft_bins = int(np.fft.rfft(np.zeros(n_bins)).shape[0])
    edges = _band_edges(n_fft_bins, int(n_bands))

    P = np.zeros((n_frames, int(n_bands)), dtype=float)
    H = np.zeros((n_frames,), dtype=float)

    for t in range(n_frames):
        power = _spectral_power_rfft(X[t])
        Eb = []
        for i in range(len(edges) - 1):
            s, e = int(edges[i]), int(edges[i + 1])
            Eb.append(float(np.sum(power[s:e])))
        Eb_arr = np.asarray(Eb, dtype=float)
        p = Eb_arr / (float(np.sum(Eb_arr)) + float(eps))
        P[t, :] = p
        H[t] = _entropy_normalized(p, eps=float(eps))

    dH = np.diff(H)
    dP = np.diff(P, axis=0)

    # Modulation time series (aligned with diffs)
    mod = np.mean(np.abs(dP), axis=1)

    # Drift series (JS divergence between adjacent p vectors)
    drift_js = np.zeros((n_frames - 1,), dtype=float)
    for t in range(1, n_frames):
        drift_js[t - 1] = _js_divergence(P[t - 1], P[t], eps=float(eps))

    per_band_corr_H_P = [
        _pearson_corr(H, P[:, b], eps=float(eps)) for b in range(int(n_bands))
    ]
    per_band_corr_dH_dP = [
        _pearson_corr(dH, dP[:, b], eps=float(eps)) for b in range(int(n_bands))
    ]

    # Align H with mod (both indexed by transitions t-1 -> t)
    corr_H_mod = _pearson_corr(H[1:], mod, eps=float(eps))
    corr_dH_mod = _pearson_corr(dH, mod, eps=float(eps))

    lag_rows, best_lag, best_corr = _lag_scan_corr(dH, mod, max_lag=int(max_lag), eps=float(eps))

    corr_abs_dH_drift = _pearson_corr(np.abs(dH), drift_js, eps=float(eps))

    series_entropy = None
    series_mod = None
    series_drift = None
    if n_frames <= int(include_series_limit):
        series_entropy = [float(v) for v in H.tolist()]
        series_mod = [float(v) for v in mod.tolist()]
        series_drift = [float(v) for v in drift_js.tolist()]

    return OVUCFF07CrossMetricCouplingReport(
        schema="OV-UCFF-07/cross_metric_coupling_report/v1",
        config_tag=str(config_tag),
        eps=float(eps),
        n_frames=n_frames,
        n_bins=n_bins,
        n_fft_bins=n_fft_bins,
        n_bands=int(n_bands),
        band_edges=[int(v) for v in edges],
        dt=float(dt),
        max_lag=int(max_lag),
        entropy_norm_mean=float(np.mean(H)),
        modulation_mean=float(np.mean(mod)),
        drift_js_mean=float(np.mean(drift_js)),
        per_band_corr_entropy_frac=[float(v) for v in per_band_corr_H_P],
        per_band_corr_dentropy_dfrac=[float(v) for v in per_band_corr_dH_dP],
        corr_entropy_modulation=float(corr_H_mod),
        corr_dentropy_modulation=float(corr_dH_mod),
        lag_scan_dentropy_modulation=lag_rows,
        best_lag_dentropy_modulation=int(best_lag),
        best_corr_dentropy_modulation=float(best_corr),
        corr_abs_dentropy_drift_js=float(corr_abs_dH_drift),
        series_entropy_norm=series_entropy,
        series_modulation_mean_abs_dfrac=series_mod,
        series_drift_js=series_drift,
    )


def default_demo_inputs() -> dict[str, np.ndarray]:
    n_bins = 256
    n_frames = 32
    i = np.arange(n_bins, dtype=float)

    constant = np.tile(np.ones(n_bins, dtype=float), (n_frames, 1))

    # Increasing high-frequency mixture shifts band fractions deterministically.
    k_low = 3.0
    k_high = 40.0
    base_low = np.sin(2.0 * np.pi * k_low * i / float(n_bins))
    base_high = np.sin(2.0 * np.pi * k_high * i / float(n_bins))
    mix = []
    for t in range(n_frames):
        w = float(t) / float(max(1, n_frames - 1))
        mix.append(base_low + w * base_high)
    mixed = np.asarray(mix, dtype=float)

    rng = np.random.default_rng(0)
    noise = rng.standard_normal((n_frames, n_bins)).astype(float)

    return {"constant": constant, "mixed": mixed, "noise": noise}


def default_pinned_input_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "input"
        / "OV-UCFF-07"
        / "legacy_phase51_coherence_drift_density_sequence.json"
    )


def load_pinned_input_payload(*, path: Path | None = None) -> dict[str, Any]:
    p = default_pinned_input_path() if path is None else Path(path)
    raw = json.loads(p.read_text(encoding="utf-8"))
    X = raw.get("X")
    if not isinstance(X, list):
        raise ValueError("pinned input JSON must contain key 'X' as a 2D list")
    dt = raw.get("dt")
    payload: dict[str, Any] = {
        "path": p.as_posix(),
        "dt": (1.0 if dt is None else float(dt)),
        "X": _as_2d_float(np.asarray(X, dtype=float)),
    }
    return payload


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "diagnostics"
        / "OV-UCFF-07"
        / "ucff_cross_metric_coupling.json"
    )


def write_ovucff07_cross_metric_coupling_artifact(*, path: Path | None = None) -> Path:
    demo = default_demo_inputs()

    pinned_path = default_pinned_input_path()
    pinned_block: dict[str, Any] | None = None
    pinned_rep: dict[str, Any] | None = None

    if pinned_path.exists():
        pinned_payload = load_pinned_input_payload(path=pinned_path)
        Xp = pinned_payload["X"]
        dtp = pinned_payload["dt"]
        pinned_block = {
            "path": pinned_path.as_posix(),
            "schema": "OV-UCFF-07/pinned_input_density_sequence/v1",
            "shape": [int(Xp.shape[0]), int(Xp.shape[1])],
            "dt": dtp,
        }
        pinned_rep = ovucff07_cross_metric_coupling_audit(
            X=Xp,
            dt=float(dtp),
        ).to_jsonable()

    rep_constant = ovucff07_cross_metric_coupling_audit(X=demo["constant"], dt=1.0).to_jsonable()
    rep_mixed = ovucff07_cross_metric_coupling_audit(X=demo["mixed"], dt=1.0).to_jsonable()
    rep_noise = ovucff07_cross_metric_coupling_audit(X=demo["noise"], dt=1.0).to_jsonable()

    payload: dict[str, Any] = {
        "schema": "OV-UCFF-07/cross_metric_coupling_artifact/v1",
        "notes": (
            "Bookkeeping only. Includes (a) an optional pinned, legacy-derived internal input report if present, "
            "plus (b) synthetic demo reports used for regression coverage. Not external evidence and not a UCFF physics claim."
        ),
        "pinned_input": pinned_block,
        "reports": {
            "pinned": pinned_rep,
            "demo_constant": rep_constant,
            "demo_mixed": rep_mixed,
            "demo_noise": rep_noise,
        },
        "demo_inputs": {
            "constant": demo["constant"].tolist(),
            "mixed": demo["mixed"].tolist(),
            "noise": demo["noise"].tolist(),
        },
    }
    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
