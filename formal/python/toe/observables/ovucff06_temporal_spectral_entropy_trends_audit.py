"""OV-UCFF-06: Temporal spectral entropy trends audit scaffold.

This module tracks how spectral *disorder* (via normalized band-energy entropy)
changes across frames.

Overview (bookkeeping only)
- For each frame x_t, compute rFFT power |FFT(x_t)|^2.
- Partition rFFT bins into n_bands contiguous bands.
- Convert per-band energy to a normalized distribution p_t.
- Compute normalized entropy H_t in [0,1] per frame.
- Summarize temporal behavior:
  - mean / min / max of H_t
  - mean absolute adjacent delta of H_t
  - linear trend slope of H_t vs time (dt)

Policy / limits
- Not an empirical anchor.
- Does not assert UCFF physics; it records deterministic numeric summaries.
- Supports a pinned, legacy-derived internal input sequence.
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


def _entropy_normalized(p: np.ndarray, *, eps: float) -> float:
    p = np.asarray(p, dtype=float)
    p = p / (float(np.sum(p)) + float(eps))
    n = int(p.size)
    if n <= 1:
        return 0.0
    H = -float(np.sum(p * np.log(p + float(eps))))
    return float(H / np.log(float(n)))


@dataclass(frozen=True)
class OVUCFF06EntropyTrendsReport:
    schema: str
    config_tag: str
    eps: float
    n_frames: int
    n_bins: int
    n_fft_bins: int
    n_bands: int
    band_edges: list[int]
    dt: float

    entropy_norm_mean: float
    entropy_norm_min: float
    entropy_norm_max: float
    entropy_norm_mean_abs_delta: float
    entropy_norm_trend_slope: float

    per_frame_entropy_norm: list[float] | None

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovucff06_temporal_spectral_entropy_trends_audit(
    *,
    X: np.ndarray,
    n_bands: int = 8,
    dt: float = 1.0,
    eps: float = 1e-12,
    config_tag: str = "OV-UCFF-06_entropy_trends_v1",
    include_per_frame_limit: int = 256,
) -> OVUCFF06EntropyTrendsReport:
    X = _as_2d_float(X)
    if dt <= 0:
        raise ValueError("dt must be > 0")
    if eps <= 0:
        raise ValueError("eps must be > 0")

    n_frames, n_bins = int(X.shape[0]), int(X.shape[1])
    n_fft_bins = int(np.fft.rfft(np.zeros(n_bins)).shape[0])
    edges = _band_edges(n_fft_bins, int(n_bands))

    H: list[float] = []

    for t in range(n_frames):
        power = _spectral_power_rfft(X[t])
        Eb = []
        for i in range(len(edges) - 1):
            s, e = int(edges[i]), int(edges[i + 1])
            Eb.append(float(np.sum(power[s:e])))
        Eb_arr = np.asarray(Eb, dtype=float)
        p = Eb_arr / (float(np.sum(Eb_arr)) + float(eps))
        H.append(_entropy_normalized(p, eps=float(eps)))

    H_arr = np.asarray(H, dtype=float)
    dH = np.diff(H_arr)
    mad = float(np.mean(np.abs(dH))) if dH.size else 0.0

    # Linear trend slope vs time (t*dt)
    tvals = np.arange(n_frames, dtype=float) * float(dt)
    m, _b = np.polyfit(tvals, H_arr, deg=1)

    per_frame = None
    if n_frames <= int(include_per_frame_limit):
        per_frame = [float(v) for v in H_arr.tolist()]

    return OVUCFF06EntropyTrendsReport(
        schema="OV-UCFF-06/entropy_trends_report/v1",
        config_tag=str(config_tag),
        eps=float(eps),
        n_frames=n_frames,
        n_bins=n_bins,
        n_fft_bins=n_fft_bins,
        n_bands=int(n_bands),
        band_edges=[int(v) for v in edges],
        dt=float(dt),
        entropy_norm_mean=float(np.mean(H_arr)),
        entropy_norm_min=float(np.min(H_arr)),
        entropy_norm_max=float(np.max(H_arr)),
        entropy_norm_mean_abs_delta=float(mad),
        entropy_norm_trend_slope=float(m),
        per_frame_entropy_norm=per_frame,
    )


def default_demo_inputs() -> dict[str, np.ndarray]:
    n_bins = 256
    n_frames = 32
    i = np.arange(n_bins, dtype=float)

    constant = np.tile(np.ones(n_bins, dtype=float), (n_frames, 1))

    # Increasing high-frequency mixture tends to increase entropy.
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
        / "OV-UCFF-06"
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
        / "OV-UCFF-06"
        / "ucff_entropy_trends.json"
    )


def write_ovucff06_entropy_trends_artifact(*, path: Path | None = None) -> Path:
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
            "schema": "OV-UCFF-06/pinned_input_density_sequence/v1",
            "shape": [int(Xp.shape[0]), int(Xp.shape[1])],
            "dt": dtp,
        }
        pinned_rep = ovucff06_temporal_spectral_entropy_trends_audit(
            X=Xp,
            dt=float(dtp),
        ).to_jsonable()

    rep_constant = ovucff06_temporal_spectral_entropy_trends_audit(X=demo["constant"], dt=1.0).to_jsonable()
    rep_mixed = ovucff06_temporal_spectral_entropy_trends_audit(X=demo["mixed"], dt=1.0).to_jsonable()
    rep_noise = ovucff06_temporal_spectral_entropy_trends_audit(X=demo["noise"], dt=1.0).to_jsonable()

    payload: dict[str, Any] = {
        "schema": "OV-UCFF-06/entropy_trends_artifact/v1",
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
