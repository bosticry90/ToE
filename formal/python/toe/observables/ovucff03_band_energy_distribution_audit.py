"""OV-UCFF-03: Band energy distribution audit scaffold.

This module computes bookkeeping metrics about how spectral energy is distributed
across frequency bands, frame-by-frame, for an input matrix X with shape
(n_frames, n_bins).

Overview (bookkeeping only)
- For each frame x, compute rFFT power spectrum |FFT(x)|^2.
- Partition rFFT bins into n_bands contiguous bands.
- Compute per-band energy E_b and normalized distribution p_b.
- Summarize distribution shape via:
  - Normalized entropy (0..1)
  - Spectral flatness (geometric mean / arithmetic mean over bands)
  - Log-log slope of band energy vs band index (heuristic)

Legacy continuity option
- Optionally compute a 3-band partition over physical wavenumber k with thresholds
    (k_low, k_mid), matching the locked turbulence diagnostics convention:
        E_k = |rfft(field)|^2 / N^2
    and sum(E_k) over low/mid/high masks.

Policy / limits
- Not an empirical anchor.
- Does not assert UCFF physics; it records deterministic numeric summaries.
- Supports an optional pinned, legacy-derived internal input artifact.

If/when more specific legacy metrics are located (e.g. explicit "energy slope"
reports), this scaffold can be tightened to match them.
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
    if a.shape[0] < 1:
        raise ValueError("need at least 1 frame")
    if a.shape[1] < 2:
        raise ValueError("need at least 2 bins")
    return a


def _band_edges(n_bins: int, n_bands: int) -> list[int]:
    if n_bands < 2:
        raise ValueError("n_bands must be >= 2")
    if n_bins < n_bands:
        raise ValueError("n_bands must be <= number of rFFT bins")

    # Equal-width partition in index space.
    edges = np.linspace(0, n_bins, n_bands + 1, dtype=int).tolist()

    # Ensure strictly increasing edges.
    for i in range(1, len(edges)):
        if edges[i] <= edges[i - 1]:
            edges[i] = edges[i - 1] + 1
    edges[-1] = n_bins

    # If the last adjustment overflowed, fall back to a simple 1-step partition.
    if edges[-1] != n_bins or len(set(edges)) != len(edges):
        edges = list(range(0, n_bands)) + [n_bins]
        # spread remaining bins across the final edge only; ensures monotone.
        for i in range(1, n_bands):
            edges[i] = i

    return edges


def _spectral_power_rfft(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x, dtype=float).ravel()
    F = np.fft.rfft(x)
    return np.abs(F) ** 2


def _legacy_spectrum_k_and_Ek(field: np.ndarray, *, dx: float) -> tuple[np.ndarray, np.ndarray]:
    """Locked turbulence diagnostics convention: k from rfftfreq, E_k = |F|^2 / N^2."""

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


def _entropy_normalized(p: np.ndarray, *, eps: float) -> float:
    p = np.asarray(p, dtype=float)
    p = p / (float(np.sum(p)) + float(eps))
    n = int(p.size)
    if n <= 1:
        return 0.0
    H = -float(np.sum(p * np.log(p + float(eps))))
    return float(H / np.log(float(n)))


def _flatness(E: np.ndarray, *, eps: float) -> float:
    E = np.asarray(E, dtype=float)
    E = E + float(eps)
    gm = float(np.exp(np.mean(np.log(E))))
    am = float(np.mean(E))
    return float(gm / am)


def _loglog_slope(E: np.ndarray, *, eps: float) -> float:
    # Use band index + 1 (avoids log(0)); slope is a heuristic shape metric.
    E = np.asarray(E, dtype=float) + float(eps)
    x = np.log10(np.arange(1, E.size + 1, dtype=float))
    y = np.log10(E)
    m, _b = np.polyfit(x, y, deg=1)
    return float(m)


@dataclass(frozen=True)
class OVUCFF03BandEnergyDistributionReport:
    schema: str
    config_tag: str
    eps: float
    n_frames: int
    n_bins: int
    n_fft_bins: int
    n_bands: int
    band_edges: list[int]
    band_energy_mean: list[float]
    band_energy_norm_mean: list[float]
    entropy_norm_mean: float
    entropy_norm_min: float
    flatness_mean: float
    flatness_min: float
    energy_slope_mean: float
    energy_slope_min: float
    legacy_k_low: float | None
    legacy_k_mid: float | None
    legacy_dx: float | None
    legacy_E_frac_low_mean: float | None
    legacy_E_frac_mid_mean: float | None
    legacy_E_frac_high_mean: float | None
    legacy_E_frac_mid_min: float | None
    per_frame: list[dict[str, Any]] | None

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovucff03_band_energy_distribution_audit(
    *,
    X: np.ndarray,
    n_bands: int = 8,
    eps: float = 1e-12,
    config_tag: str = "OV-UCFF-03_band_energy_distribution_v1",
    include_per_frame_limit: int = 64,
    legacy_k_low: float | None = None,
    legacy_k_mid: float | None = None,
    dx: float | None = None,
) -> OVUCFF03BandEnergyDistributionReport:
    X = _as_2d_float(X)
    if eps <= 0:
        raise ValueError("eps must be > 0")

    n_frames, n_bins = int(X.shape[0]), int(X.shape[1])

    # rFFT bins count includes DC and Nyquist (if even length).
    n_fft_bins = int(np.fft.rfft(np.zeros(n_bins)).shape[0])
    edges = _band_edges(n_fft_bins, int(n_bands))

    band_E = []
    ent = []
    flat = []
    slope = []
    legacy_frac_low: list[float] = []
    legacy_frac_mid: list[float] = []
    legacy_frac_high: list[float] = []
    per_frame: list[dict[str, Any]] = []

    do_legacy = legacy_k_low is not None and legacy_k_mid is not None
    legacy_dx = 1.0 if dx is None else float(dx)

    for t in range(n_frames):
        power = _spectral_power_rfft(X[t])

        Eb = []
        for i in range(len(edges) - 1):
            s, e = int(edges[i]), int(edges[i + 1])
            Eb.append(float(np.sum(power[s:e])))

        Eb_arr = np.asarray(Eb, dtype=float)
        total = float(np.sum(Eb_arr)) + float(eps)
        pb = Eb_arr / total

        ent_t = _entropy_normalized(pb, eps=float(eps))
        flat_t = _flatness(Eb_arr, eps=float(eps))
        slope_t = _loglog_slope(Eb_arr, eps=float(eps))

        band_E.append(Eb_arr)
        ent.append(ent_t)
        flat.append(flat_t)
        slope.append(slope_t)

        if do_legacy:
            k, E_k = _legacy_spectrum_k_and_Ek(X[t], dx=float(legacy_dx))
            E_low, E_mid, E_high, E_tot = _legacy_partition_spectrum_1d(
                k=k,
                E_k=E_k,
                k_low=float(legacy_k_low),
                k_mid=float(legacy_k_mid),
            )
            denom = float(E_tot) + float(eps)
            legacy_frac_low.append(float(E_low / denom))
            legacy_frac_mid.append(float(E_mid / denom))
            legacy_frac_high.append(float(E_high / denom))

        if n_frames <= int(include_per_frame_limit):
            per_frame.append(
                {
                    "t": int(t),
                    "entropy_norm": float(ent_t),
                    "flatness": float(flat_t),
                    "energy_slope": float(slope_t),
                    "band_energy": [float(v) for v in Eb_arr.tolist()],
                    "band_energy_norm": [float(v) for v in pb.tolist()],
                    "legacy_three_band": (
                        None
                        if not do_legacy
                        else {
                            "k_low": float(legacy_k_low),
                            "k_mid": float(legacy_k_mid),
                            "dx": float(legacy_dx),
                            "E_frac_low": float(legacy_frac_low[-1]),
                            "E_frac_mid": float(legacy_frac_mid[-1]),
                            "E_frac_high": float(legacy_frac_high[-1]),
                        }
                    ),
                }
            )

    band_E_mat = np.vstack(band_E)
    band_E_mean = np.mean(band_E_mat, axis=0)

    # Mean normalized distribution over frames.
    norm_mat = band_E_mat / (np.sum(band_E_mat, axis=1, keepdims=True) + float(eps))
    norm_mean = np.mean(norm_mat, axis=0)

    ent_arr = np.asarray(ent, dtype=float)
    flat_arr = np.asarray(flat, dtype=float)
    slope_arr = np.asarray(slope, dtype=float)

    legacy_mean_low = legacy_mean_mid = legacy_mean_high = legacy_min_mid = None
    if do_legacy:
        legacy_mean_low = float(np.mean(np.asarray(legacy_frac_low, dtype=float)))
        legacy_mean_mid = float(np.mean(np.asarray(legacy_frac_mid, dtype=float)))
        legacy_mean_high = float(np.mean(np.asarray(legacy_frac_high, dtype=float)))
        legacy_min_mid = float(np.min(np.asarray(legacy_frac_mid, dtype=float)))

    return OVUCFF03BandEnergyDistributionReport(
        schema="OV-UCFF-03/band_energy_distribution_report/v2",
        config_tag=str(config_tag),
        eps=float(eps),
        n_frames=n_frames,
        n_bins=n_bins,
        n_fft_bins=n_fft_bins,
        n_bands=int(n_bands),
        band_edges=[int(v) for v in edges],
        band_energy_mean=[float(v) for v in band_E_mean.tolist()],
        band_energy_norm_mean=[float(v) for v in norm_mean.tolist()],
        entropy_norm_mean=float(np.mean(ent_arr)),
        entropy_norm_min=float(np.min(ent_arr)),
        flatness_mean=float(np.mean(flat_arr)),
        flatness_min=float(np.min(flat_arr)),
        energy_slope_mean=float(np.mean(slope_arr)),
        energy_slope_min=float(np.min(slope_arr)),
        legacy_k_low=(None if not do_legacy else float(legacy_k_low)),
        legacy_k_mid=(None if not do_legacy else float(legacy_k_mid)),
        legacy_dx=(None if not do_legacy else float(legacy_dx)),
        legacy_E_frac_low_mean=legacy_mean_low,
        legacy_E_frac_mid_mean=legacy_mean_mid,
        legacy_E_frac_high_mean=legacy_mean_high,
        legacy_E_frac_mid_min=legacy_min_mid,
        per_frame=(per_frame if n_frames <= int(include_per_frame_limit) else None),
    )


def default_demo_inputs() -> dict[str, np.ndarray]:
    """Return canonical demo inputs for testing and artifact generation."""

    dc = np.tile(np.ones(256, dtype=float), (2, 1))

    rng = np.random.default_rng(0)
    noise = rng.standard_normal((2, 256)).astype(float)

    return {"dc": dc, "noise": noise}


def default_pinned_input_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "input"
        / "OV-UCFF-03"
        / "legacy_phase51_coherence_drift_pair_density.json"
    )


def load_pinned_input_X(*, path: Path | None = None) -> np.ndarray:
    p = default_pinned_input_path() if path is None else Path(path)
    raw = json.loads(p.read_text(encoding="utf-8"))
    X = raw.get("X")
    if not isinstance(X, list):
        raise ValueError("pinned input JSON must contain key 'X' as a 2D list")
    return _as_2d_float(np.asarray(X, dtype=float))


def load_pinned_input_payload(*, path: Path | None = None) -> dict[str, Any]:
    p = default_pinned_input_path() if path is None else Path(path)
    raw = json.loads(p.read_text(encoding="utf-8"))
    X = raw.get("X")
    if not isinstance(X, list):
        raise ValueError("pinned input JSON must contain key 'X' as a 2D list")
    dx = raw.get("dx")
    payload: dict[str, Any] = {
        "path": p.as_posix(),
        "dx": (None if dx is None else float(dx)),
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
        / "OV-UCFF-03"
        / "ucff_band_energy_distribution.json"
    )


def write_ovucff03_band_energy_distribution_artifact(*, path: Path | None = None) -> Path:
    demo = default_demo_inputs()

    pinned_path = default_pinned_input_path()
    pinned_block: dict[str, Any] | None = None
    pinned_rep: dict[str, Any] | None = None

    if pinned_path.exists():
        pinned_payload = load_pinned_input_payload(path=pinned_path)
        Xp = pinned_payload["X"]
        dxp = pinned_payload["dx"]
        pinned_block = {
            "path": pinned_path.as_posix(),
            "schema": "OV-UCFF-03/pinned_input_density_pair/v1",
            "shape": [int(Xp.shape[0]), int(Xp.shape[1])],
            "dx": dxp,
        }
        pinned_rep = ovucff03_band_energy_distribution_audit(
            X=Xp,
            dx=dxp,
            legacy_k_low=2.0,
            legacy_k_mid=6.0,
        ).to_jsonable()

    rep_dc = ovucff03_band_energy_distribution_audit(
        X=demo["dc"],
        dx=1.0,
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    ).to_jsonable()
    rep_noise = ovucff03_band_energy_distribution_audit(
        X=demo["noise"],
        dx=1.0,
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    ).to_jsonable()

    payload: dict[str, Any] = {
        "schema": "OV-UCFF-03/band_energy_distribution_artifact/v1",
        "notes": (
            "Bookkeeping only. Includes (a) an optional pinned, legacy-derived internal input report if present, "
            "plus (b) synthetic demo reports used for regression coverage. Not external evidence and not a UCFF physics claim."
        ),
        "pinned_input": pinned_block,
        "reports": {
            "pinned": pinned_rep,
            "demo_dc": rep_dc,
            "demo_noise": rep_noise,
        },
        "demo_inputs": {
            "dc": demo["dc"].tolist(),
            "noise": demo["noise"].tolist(),
        },
    }
    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
