"""OV-UCFF-04: Spectral evolution audit scaffold.

This module extends OV-UCFF-03 (static spectral fingerprint) by measuring how the
spectral shape evolves across frames.

Overview (bookkeeping only)
- For each frame x, compute rFFT power spectrum |FFT(x)|^2.
- Partition rFFT bins into n_bands contiguous bands and normalize to a per-frame
  band-energy distribution p (a discrete probability vector).
- Compute adjacent-frame drift metrics:
  - L2 distance: ||p_t - p_{t+1}||_2
  - Cosine distance: 1 - cos(p_t, p_{t+1})
  - Jensen–Shannon divergence (natural log base)
  - Delta of per-frame shape scalars: entropy_norm, energy_slope

Legacy continuity option
- Optionally compute locked turbulence-style 3-band (k_low/k_mid) fractions per
  frame and report their adjacent deltas.

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
        raise ValueError("need at least 2 frames for evolution metrics")
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


def _loglog_slope(E: np.ndarray, *, eps: float) -> float:
    E = np.asarray(E, dtype=float) + float(eps)
    x = np.log10(np.arange(1, E.size + 1, dtype=float))
    y = np.log10(E)
    m, _b = np.polyfit(x, y, deg=1)
    return float(m)


def _cosine_distance(a: np.ndarray, b: np.ndarray, *, eps: float) -> float:
    a = np.asarray(a, dtype=float).ravel()
    b = np.asarray(b, dtype=float).ravel()
    na = float(np.linalg.norm(a))
    nb = float(np.linalg.norm(b))
    denom = float(na * nb)
    if denom <= float(eps):
        return 0.0
    cos = float(np.dot(a, b) / denom)
    # Numerical guard: keep within [-1, 1]
    cos = max(-1.0, min(1.0, cos))
    return float(1.0 - cos)


def _js_divergence(p: np.ndarray, q: np.ndarray, *, eps: float) -> float:
    p = np.asarray(p, dtype=float).ravel()
    q = np.asarray(q, dtype=float).ravel()
    p = p / (float(np.sum(p)) + float(eps))
    q = q / (float(np.sum(q)) + float(eps))
    m = 0.5 * (p + q)

    def _kl(a: np.ndarray, b: np.ndarray) -> float:
        a = a + float(eps)
        b = b + float(eps)
        return float(np.sum(a * np.log(a / b)))

    return 0.5 * _kl(p, m) + 0.5 * _kl(q, m)


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
class OVUCFF04SpectralEvolutionReport:
    schema: str
    config_tag: str
    eps: float
    n_frames: int
    n_bins: int
    n_fft_bins: int
    n_bands: int
    band_edges: list[int]

    l2_drift_mean: float
    l2_drift_max: float
    cosine_dist_mean: float
    cosine_dist_max: float
    js_div_mean: float
    js_div_max: float

    delta_entropy_norm_mean: float
    delta_entropy_norm_max: float
    delta_energy_slope_mean: float
    delta_energy_slope_max: float

    legacy_k_low: float | None
    legacy_k_mid: float | None
    legacy_dx: float | None
    legacy_delta_E_frac_mid_abs_mean: float | None
    legacy_delta_E_frac_mid_abs_max: float | None

    per_pair: list[dict[str, Any]] | None

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovucff04_spectral_evolution_audit(
    *,
    X: np.ndarray,
    n_bands: int = 8,
    eps: float = 1e-12,
    config_tag: str = "OV-UCFF-04_spectral_evolution_v1",
    include_per_pair_limit: int = 64,
    legacy_k_low: float | None = None,
    legacy_k_mid: float | None = None,
    dx: float | None = None,
) -> OVUCFF04SpectralEvolutionReport:
    X = _as_2d_float(X)
    if eps <= 0:
        raise ValueError("eps must be > 0")

    n_frames, n_bins = int(X.shape[0]), int(X.shape[1])
    n_fft_bins = int(np.fft.rfft(np.zeros(n_bins)).shape[0])
    edges = _band_edges(n_fft_bins, int(n_bands))

    do_legacy = legacy_k_low is not None and legacy_k_mid is not None
    legacy_dx = 1.0 if dx is None else float(dx)

    per_frame_p: list[np.ndarray] = []
    per_frame_entropy: list[float] = []
    per_frame_slope: list[float] = []
    per_frame_legacy_mid: list[float] = []

    for t in range(n_frames):
        power = _spectral_power_rfft(X[t])
        Eb = []
        for i in range(len(edges) - 1):
            s, e = int(edges[i]), int(edges[i + 1])
            Eb.append(float(np.sum(power[s:e])))
        Eb_arr = np.asarray(Eb, dtype=float)
        total = float(np.sum(Eb_arr)) + float(eps)
        p = Eb_arr / total

        per_frame_p.append(p)
        per_frame_entropy.append(_entropy_normalized(p, eps=float(eps)))
        per_frame_slope.append(_loglog_slope(Eb_arr, eps=float(eps)))

        if do_legacy:
            k, E_k = _legacy_spectrum_k_and_Ek(X[t], dx=float(legacy_dx))
            _E_low, E_mid, _E_high, E_tot = _legacy_partition_spectrum_1d(
                k=k,
                E_k=E_k,
                k_low=float(legacy_k_low),
                k_mid=float(legacy_k_mid),
            )
            per_frame_legacy_mid.append(float(E_mid / (float(E_tot) + float(eps))))

    l2_list: list[float] = []
    cos_list: list[float] = []
    js_list: list[float] = []
    dH_list: list[float] = []
    dS_list: list[float] = []
    dMid_list: list[float] = []
    per_pair: list[dict[str, Any]] = []

    n_pairs = n_frames - 1
    for t in range(n_pairs):
        p0 = per_frame_p[t]
        p1 = per_frame_p[t + 1]

        l2 = float(np.linalg.norm(p1 - p0))
        cosd = _cosine_distance(p0, p1, eps=float(eps))
        jsd = _js_divergence(p0, p1, eps=float(eps))

        dH = float(per_frame_entropy[t + 1] - per_frame_entropy[t])
        dS = float(per_frame_slope[t + 1] - per_frame_slope[t])

        l2_list.append(l2)
        cos_list.append(cosd)
        js_list.append(jsd)
        dH_list.append(dH)
        dS_list.append(dS)

        legacy_mid = None
        if do_legacy:
            dmid = float(per_frame_legacy_mid[t + 1] - per_frame_legacy_mid[t])
            dMid_list.append(abs(dmid))
            legacy_mid = {
                "E_frac_mid_t": float(per_frame_legacy_mid[t]),
                "E_frac_mid_t1": float(per_frame_legacy_mid[t + 1]),
                "delta_E_frac_mid": float(dmid),
            }

        if n_pairs <= int(include_per_pair_limit):
            per_pair.append(
                {
                    "t": int(t),
                    "t1": int(t + 1),
                    "l2": float(l2),
                    "cosine_dist": float(cosd),
                    "js_div": float(jsd),
                    "delta_entropy_norm": float(dH),
                    "delta_energy_slope": float(dS),
                    "legacy_three_band_mid": legacy_mid,
                }
            )

    l2_arr = np.asarray(l2_list, dtype=float)
    cos_arr = np.asarray(cos_list, dtype=float)
    js_arr = np.asarray(js_list, dtype=float)
    dH_arr = np.asarray(dH_list, dtype=float)
    dS_arr = np.asarray(dS_list, dtype=float)

    legacy_mid_mean = legacy_mid_max = None
    if do_legacy:
        dm = np.asarray(dMid_list, dtype=float)
        legacy_mid_mean = float(np.mean(dm))
        legacy_mid_max = float(np.max(dm))

    return OVUCFF04SpectralEvolutionReport(
        schema="OV-UCFF-04/spectral_evolution_report/v1",
        config_tag=str(config_tag),
        eps=float(eps),
        n_frames=n_frames,
        n_bins=n_bins,
        n_fft_bins=n_fft_bins,
        n_bands=int(n_bands),
        band_edges=[int(v) for v in edges],
        l2_drift_mean=float(np.mean(l2_arr)),
        l2_drift_max=float(np.max(l2_arr)),
        cosine_dist_mean=float(np.mean(cos_arr)),
        cosine_dist_max=float(np.max(cos_arr)),
        js_div_mean=float(np.mean(js_arr)),
        js_div_max=float(np.max(js_arr)),
        delta_entropy_norm_mean=float(np.mean(np.abs(dH_arr))),
        delta_entropy_norm_max=float(np.max(np.abs(dH_arr))),
        delta_energy_slope_mean=float(np.mean(np.abs(dS_arr))),
        delta_energy_slope_max=float(np.max(np.abs(dS_arr))),
        legacy_k_low=(None if not do_legacy else float(legacy_k_low)),
        legacy_k_mid=(None if not do_legacy else float(legacy_k_mid)),
        legacy_dx=(None if not do_legacy else float(legacy_dx)),
        legacy_delta_E_frac_mid_abs_mean=legacy_mid_mean,
        legacy_delta_E_frac_mid_abs_max=legacy_mid_max,
        per_pair=(per_pair if n_pairs <= int(include_per_pair_limit) else None),
    )


def default_demo_inputs() -> dict[str, np.ndarray]:
    n = 256
    i = np.arange(n, dtype=float)

    constant = np.tile(np.ones(n, dtype=float), (3, 1))

    # Drift: shift energy between a low-frequency and a higher-frequency component.
    k_low = 3.0
    k_high = 40.0
    base_low = np.sin(2.0 * np.pi * k_low * i / float(n))
    base_high = np.sin(2.0 * np.pi * k_high * i / float(n))
    weights = [0.0, 0.5, 1.0]
    drift_arr = np.asarray([base_low + w * base_high for w in weights], dtype=float)

    rng = np.random.default_rng(0)
    noise = rng.standard_normal((3, n)).astype(float)

    return {"constant": constant, "drift": drift_arr, "noise": noise}


def default_pinned_input_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "input"
        / "OV-UCFF-04"
        / "legacy_phase51_coherence_drift_pair_density.json"
    )


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
        / "OV-UCFF-04"
        / "ucff_spectral_evolution.json"
    )


def write_ovucff04_spectral_evolution_artifact(*, path: Path | None = None) -> Path:
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
            "schema": "OV-UCFF-04/pinned_input_density_pair/v1",
            "shape": [int(Xp.shape[0]), int(Xp.shape[1])],
            "dx": dxp,
        }
        pinned_rep = ovucff04_spectral_evolution_audit(
            X=Xp,
            dx=dxp,
            legacy_k_low=2.0,
            legacy_k_mid=6.0,
        ).to_jsonable()

    rep_constant = ovucff04_spectral_evolution_audit(
        X=demo["constant"],
        dx=1.0,
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    ).to_jsonable()
    rep_drift = ovucff04_spectral_evolution_audit(
        X=demo["drift"],
        dx=1.0,
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    ).to_jsonable()
    rep_noise = ovucff04_spectral_evolution_audit(
        X=demo["noise"],
        dx=1.0,
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    ).to_jsonable()

    payload: dict[str, Any] = {
        "schema": "OV-UCFF-04/spectral_evolution_artifact/v1",
        "notes": (
            "Bookkeeping only. Includes (a) an optional pinned, legacy-derived internal input report if present, "
            "plus (b) synthetic demo reports used for regression coverage. Not external evidence and not a UCFF physics claim."
        ),
        "pinned_input": pinned_block,
        "reports": {
            "pinned": pinned_rep,
            "demo_constant": rep_constant,
            "demo_drift": rep_drift,
            "demo_noise": rep_noise,
        },
        "demo_inputs": {
            "constant": demo["constant"].tolist(),
            "drift": demo["drift"].tolist(),
            "noise": demo["noise"].tolist(),
        },
    }
    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out
