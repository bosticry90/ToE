"""OV-UCFF-05: Temporal band modulation audit scaffold.

This module extends the UCFF spectral audit series by analyzing *temporal* structure
in the per-band energy time series.

Overview (bookkeeping only)
- For each frame x_t, compute rFFT power |FFT(x_t)|^2.
- Partition rFFT bins into n_bands contiguous bands.
- Build a per-frame normalized band-energy distribution p_t (a discrete
  probability vector over bands).
- For each band b, analyze the time series e_{t,b}:
  - mean / std / coefficient-of-variation
  - mean absolute adjacent delta
  - dominant temporal modulation harmonic via rFFT over time (when enough frames)
- Compute a simple cross-band coherence summary as mean absolute off-diagonal
  correlation of band time series.

Legacy continuity option
- Optionally compute locked turbulence-style 3-band (k_low/k_mid) mid-band
  fraction per frame and summarize its absolute adjacent deltas.

Policy / limits
- Not an empirical anchor.
- Does not assert UCFF physics; it records deterministic numeric summaries.
- Supports an optional pinned, legacy-derived internal input artifact.
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

    if edges[-1] != n_bins or len(set(edges)) != len(edges):
        edges = list(range(0, n_bands)) + [n_bins]
        for i in range(1, n_bands):
            edges[i] = i

    return edges


def _spectral_power_rfft(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=float).ravel()
    F = np.fft.rfft(x)
    return np.abs(F) ** 2


def _dominant_temporal_harmonic(
    ts: np.ndarray, *, dt: float, eps: float
) -> tuple[int | None, float | None, float]:
    """Return (dominant_idx, dominant_freq, dominant_strength).

    - dominant_idx: rFFT bin index in [1..] (excludes DC), or None if no modulation.
    - dominant_freq: physical frequency in cycles/unit-time (via rfftfreq), or None.
    - dominant_strength: peak_power / total_power over non-DC bins (0..1).
    """

    ts = np.asarray(ts, dtype=float).ravel()
    n = int(ts.size)
    if n < 3:
        return None, None, 0.0

    x = ts - float(np.mean(ts))
    F = np.fft.rfft(x)
    P = np.abs(F) ** 2

    if P.size <= 1:
        return None, None, 0.0

    P_ndc = P[1:]
    total = float(np.sum(P_ndc))
    if total <= float(eps):
        return None, None, 0.0

    j = int(np.argmax(P_ndc))
    dom_idx = int(j + 1)

    freqs = np.fft.rfftfreq(n, d=float(dt))
    dom_freq = float(freqs[dom_idx])

    strength = float(P_ndc[j] / total)
    return dom_idx, dom_freq, strength


def _legacy_spectrum_k_and_Ek(field: np.ndarray, *, dx: float) -> tuple[np.ndarray, np.ndarray]:
    field = np.asarray(field, dtype=float).ravel()
    N = int(field.size)
    if N < 2:
        raise ValueError("field must have at least 2 samples")
    if dx <= 0:
        raise ValueError("dx must be > 0")

    k = 2.0 * np.pi * np.fft.rfftfreq(N, d=float(dx))
    F = np.fft.rfft(field)
    E_k = (np.abs(F) ** 2) / float(N**2)
    return k, E_k


def _legacy_partition_spectrum_1d(
    *, k: np.ndarray, E_k: np.ndarray, k_low: float, k_mid: float
) -> tuple[float, float, float, float]:
    if k_low < 0 or k_mid < 0:
        raise ValueError("k_low and k_mid must be >= 0")
    if k_mid < k_low:
        raise ValueError("k_mid must be >= k_low")

    k = np.asarray(k, dtype=float)
    E_k = np.asarray(E_k, dtype=float)

    mask_low = (k >= 0.0) & (k < float(k_low))
    mask_mid = (k >= float(k_low)) & (k < float(k_mid))
    mask_high = k >= float(k_mid)

    E_low = float(np.sum(E_k[mask_low]))
    E_mid = float(np.sum(E_k[mask_mid]))
    E_high = float(np.sum(E_k[mask_high]))
    E_tot = float(np.sum(E_k))
    return E_low, E_mid, E_high, E_tot


@dataclass(frozen=True)
class OVUCFF05TemporalBandModulationReport:
    schema: str
    config_tag: str
    eps: float
    n_frames: int
    n_bins: int
    n_fft_bins: int
    n_bands: int
    band_edges: list[int]
    dt: float

    per_band_mean: list[float]
    per_band_std: list[float]
    per_band_cv: list[float]
    per_band_mean_abs_delta: list[float]

    per_band_dom_harmonic_idx: list[int | None]
    per_band_dom_harmonic_freq: list[float | None]
    per_band_dom_harmonic_strength: list[float]

    dom_strength_mean: float
    dom_strength_max: float
    cross_band_corr_abs_mean_offdiag: float

    legacy_k_low: float | None
    legacy_k_mid: float | None
    legacy_dx: float | None
    legacy_mid_frac_mean_abs_delta: float | None
    legacy_mid_frac_max_abs_delta: float | None

    per_frame_band_energy_norm: list[list[float]] | None

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovucff05_temporal_band_modulation_audit(
    *,
    X: np.ndarray,
    n_bands: int = 8,
    dt: float = 1.0,
    eps: float = 1e-12,
    config_tag: str = "OV-UCFF-05_temporal_band_modulation_v1",
    include_per_frame_limit: int = 64,
    legacy_k_low: float | None = None,
    legacy_k_mid: float | None = None,
    dx: float | None = None,
) -> OVUCFF05TemporalBandModulationReport:
    X = _as_2d_float(X)
    if dt <= 0:
        raise ValueError("dt must be > 0")
    if eps <= 0:
        raise ValueError("eps must be > 0")

    n_frames, n_bins = int(X.shape[0]), int(X.shape[1])
    n_fft_bins = int(np.fft.rfft(np.zeros(n_bins)).shape[0])
    edges = _band_edges(n_fft_bins, int(n_bands))

    do_legacy = legacy_k_low is not None and legacy_k_mid is not None
    legacy_dx = 1.0 if dx is None else float(dx)

    # Build per-frame normalized band energy distributions p_t.
    P = np.zeros((n_frames, int(n_bands)), dtype=float)
    legacy_mid: list[float] = []

    for t in range(n_frames):
        power = _spectral_power_rfft(X[t])
        Eb = []
        for i in range(len(edges) - 1):
            s, e = int(edges[i]), int(edges[i + 1])
            Eb.append(float(np.sum(power[s:e])))
        Eb_arr = np.asarray(Eb, dtype=float)
        P[t, :] = Eb_arr / (float(np.sum(Eb_arr)) + float(eps))

        if do_legacy:
            k, E_k = _legacy_spectrum_k_and_Ek(X[t], dx=float(legacy_dx))
            _E_low, E_mid, _E_high, E_tot = _legacy_partition_spectrum_1d(
                k=k,
                E_k=E_k,
                k_low=float(legacy_k_low),
                k_mid=float(legacy_k_mid),
            )
            legacy_mid.append(float(E_mid / (float(E_tot) + float(eps))))

    per_band_mean = np.mean(P, axis=0)
    per_band_std = np.std(P, axis=0)
    per_band_cv = per_band_std / (np.abs(per_band_mean) + float(eps))

    # Mean absolute adjacent deltas per band.
    dP = np.diff(P, axis=0)
    per_band_mad = np.mean(np.abs(dP), axis=0)

    dom_idx: list[int | None] = []
    dom_freq: list[float | None] = []
    dom_strength: list[float] = []

    for b in range(int(n_bands)):
        idx, f, s = _dominant_temporal_harmonic(P[:, b], dt=float(dt), eps=float(eps))
        dom_idx.append(idx)
        dom_freq.append(f)
        dom_strength.append(float(s))

    dom_strength_arr = np.asarray(dom_strength, dtype=float)

    # Cross-band correlation (mean abs off-diagonal).
    Z = (P - per_band_mean[None, :]) / (per_band_std[None, :] + float(eps))
    corr = (Z.T @ Z) / float(max(1, n_frames - 1))
    corr = np.clip(corr, -1.0, 1.0)
    abs_corr = np.abs(corr)
    off = abs_corr - np.diag(np.diag(abs_corr))
    denom = float(int(n_bands) * (int(n_bands) - 1))
    corr_abs_mean_offdiag = float(np.sum(off) / denom) if denom > 0 else 0.0

    legacy_mean_abs_delta = legacy_max_abs_delta = None
    if do_legacy and len(legacy_mid) >= 2:
        dmid = np.abs(np.diff(np.asarray(legacy_mid, dtype=float)))
        legacy_mean_abs_delta = float(np.mean(dmid))
        legacy_max_abs_delta = float(np.max(dmid))

    per_frame_out = None
    if n_frames <= int(include_per_frame_limit):
        per_frame_out = [[float(v) for v in row] for row in P.tolist()]

    return OVUCFF05TemporalBandModulationReport(
        schema="OV-UCFF-05/temporal_band_modulation_report/v1",
        config_tag=str(config_tag),
        eps=float(eps),
        n_frames=n_frames,
        n_bins=n_bins,
        n_fft_bins=n_fft_bins,
        n_bands=int(n_bands),
        band_edges=[int(v) for v in edges],
        dt=float(dt),
        per_band_mean=[float(v) for v in per_band_mean.tolist()],
        per_band_std=[float(v) for v in per_band_std.tolist()],
        per_band_cv=[float(v) for v in per_band_cv.tolist()],
        per_band_mean_abs_delta=[float(v) for v in per_band_mad.tolist()],
        per_band_dom_harmonic_idx=dom_idx,
        per_band_dom_harmonic_freq=dom_freq,
        per_band_dom_harmonic_strength=[float(v) for v in dom_strength_arr.tolist()],
        dom_strength_mean=float(np.mean(dom_strength_arr)),
        dom_strength_max=float(np.max(dom_strength_arr)),
        cross_band_corr_abs_mean_offdiag=float(corr_abs_mean_offdiag),
        legacy_k_low=(None if not do_legacy else float(legacy_k_low)),
        legacy_k_mid=(None if not do_legacy else float(legacy_k_mid)),
        legacy_dx=(None if not do_legacy else float(legacy_dx)),
        legacy_mid_frac_mean_abs_delta=legacy_mean_abs_delta,
        legacy_mid_frac_max_abs_delta=legacy_max_abs_delta,
        per_frame_band_energy_norm=per_frame_out,
    )


def default_demo_inputs() -> dict[str, np.ndarray]:
    n_bins = 256
    n_frames = 32
    i = np.arange(n_bins, dtype=float)

    constant = np.tile(np.ones(n_bins, dtype=float), (n_frames, 1))

    # Modulated: high-frequency component amplitude oscillates over time.
    k_low = 3.0
    k_high = 40.0
    base_low = np.sin(2.0 * np.pi * k_low * i / float(n_bins))
    base_high = np.sin(2.0 * np.pi * k_high * i / float(n_bins))

    mod = []
    for t in range(n_frames):
        a = 0.5 * (1.0 + np.sin(2.0 * np.pi * float(t) / 8.0))
        mod.append(base_low + a * base_high)
    modulated = np.asarray(mod, dtype=float)

    rng = np.random.default_rng(0)
    noise = rng.standard_normal((n_frames, n_bins)).astype(float)

    return {"constant": constant, "modulated": modulated, "noise": noise}


def default_pinned_input_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "input"
        / "OV-UCFF-05"
        / "legacy_phase51_coherence_drift_density_sequence.json"
    )


def load_pinned_input_payload(*, path: Path | None = None) -> dict[str, Any]:
    p = default_pinned_input_path() if path is None else Path(path)
    raw = json.loads(p.read_text(encoding="utf-8"))
    X = raw.get("X")
    if not isinstance(X, list):
        raise ValueError("pinned input JSON must contain key 'X' as a 2D list")
    dx = raw.get("dx")
    dt = raw.get("dt")
    payload: dict[str, Any] = {
        "path": p.as_posix(),
        "dx": (None if dx is None else float(dx)),
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
        / "OV-UCFF-05"
        / "ucff_temporal_band_modulation.json"
    )


def write_ovucff05_temporal_band_modulation_artifact(*, path: Path | None = None) -> Path:
    demo = default_demo_inputs()

    pinned_path = default_pinned_input_path()
    pinned_block: dict[str, Any] | None = None
    pinned_rep: dict[str, Any] | None = None

    if pinned_path.exists():
        pinned_payload = load_pinned_input_payload(path=pinned_path)
        Xp = pinned_payload["X"]
        dxp = pinned_payload["dx"]
        dtp = pinned_payload["dt"]
        pinned_block = {
            "path": pinned_path.as_posix(),
            "schema": "OV-UCFF-05/pinned_input_density_sequence/v1",
            "shape": [int(Xp.shape[0]), int(Xp.shape[1])],
            "dx": dxp,
            "dt": dtp,
        }
        pinned_rep = ovucff05_temporal_band_modulation_audit(
            X=Xp,
            dt=float(dtp),
            dx=dxp,
            legacy_k_low=2.0,
            legacy_k_mid=6.0,
        ).to_jsonable()

    rep_constant = ovucff05_temporal_band_modulation_audit(X=demo["constant"], dt=1.0).to_jsonable()
    rep_mod = ovucff05_temporal_band_modulation_audit(X=demo["modulated"], dt=1.0).to_jsonable()
    rep_noise = ovucff05_temporal_band_modulation_audit(X=demo["noise"], dt=1.0).to_jsonable()

    payload: dict[str, Any] = {
        "schema": "OV-UCFF-05/temporal_band_modulation_artifact/v1",
        "notes": (
            "Bookkeeping only. Includes (a) an optional pinned, legacy-derived internal input report if present, "
            "plus (b) synthetic demo reports used for regression coverage. Not external evidence and not a UCFF physics claim."
        ),
        "pinned_input": pinned_block,
        "reports": {
            "pinned": pinned_rep,
            "demo_constant": rep_constant,
            "demo_modulated": rep_mod,
            "demo_noise": rep_noise,
        },
        "demo_inputs": {
            "constant": demo["constant"].tolist(),
            "modulated": demo["modulated"].tolist(),
            "noise": demo["noise"].tolist(),
        },
    }
    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
