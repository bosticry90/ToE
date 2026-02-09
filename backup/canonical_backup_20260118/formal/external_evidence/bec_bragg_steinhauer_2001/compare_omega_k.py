# compare_omega_k.py
# Evidence packet comparator: Steinhauer et al. Fig. 3a vs Bogoliubov (no free parameters)
#
# Adds:
#   - single BASE_DIR
#   - sigma models: csv | placeholder | digitization
#   - outlier auto-flagging
#   - low-k sound-speed fit: c_s,fit vs c_s(mu)
#   - evidence_summary.txt includes sound-speed check + digitization-floor warning

import os
import math
from dataclasses import dataclass
from typing import Optional, Tuple

import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

# ============================
# Physical constants (SI)
# ============================
H  = 6.62607015e-34        # J·s (exact)
HB = 1.054571817e-34       # J·s
M_RB87 = 1.44316060e-25    # kg (87Rb)

MU_OVER_H_KHZ = 1.91       # caption value (no free parameters)

# ============================
# Single base directory
# ============================
BASE_DIR = os.path.join("formal", "external_evidence", "bec_bragg_steinhauer_2001")

CSV_IN      = os.path.join(BASE_DIR, "omega_k_data.csv")
CSV_OUT     = os.path.join(BASE_DIR, "comparison_results.csv")
PLOT_OUT    = os.path.join(BASE_DIR, "comparison_plot.png")
SUMMARY_OUT = os.path.join(BASE_DIR, "evidence_summary.txt")


# ============================
# Configuration
# ============================
@dataclass
class Config:
    # sigma model: csv | placeholder | digitization
    sigma_model: str

    # placeholder sigmas (kHz, um^-1)
    sigma_f_khz: float
    sigma_k_um: float

    # digitization sigma model params
    sigma_abs_floor_khz: float    # absolute floor on omega/(2pi) in kHz
    sigma_rel_frac: float         # relative fraction applied to k and f

    # outlier thresholds
    outlier_relerr_thresh: float  # |(f_exp - f_th)/f_th| > thresh
    outlier_sigma_thresh: float   # |z| > thresh, z=(resid/sigma_f)

    # sound-speed fit window
    cs_kmax_um: Optional[float]   # include points with k <= this (um^-1), if set
    cs_npts: int                  # otherwise use first N points sorted by k
    cs_fit_through_origin: bool   # True: force intercept=0 in low-k fit


def _env_float(key: str, default: float) -> float:
    v = os.environ.get(key, "").strip()
    if not v:
        return default
    try:
        return float(v)
    except ValueError:
        return default


def _env_int(key: str, default: int) -> int:
    v = os.environ.get(key, "").strip()
    if not v:
        return default
    try:
        return int(v)
    except ValueError:
        return default


def _env_bool(key: str, default: bool) -> bool:
    v = os.environ.get(key, "").strip().lower()
    if not v:
        return default
    if v in {"1", "true", "yes", "y", "on"}:
        return True
    if v in {"0", "false", "no", "n", "off"}:
        return False
    return default


def load_config() -> Config:
    sigma_model = os.environ.get("TOE_SIGMA_MODEL", "csv").lower()
    if sigma_model not in {"csv", "placeholder", "digitization"}:
        sigma_model = "csv"

    # sound-speed window: prefer explicit kmax if provided, else npts
    cs_kmax_raw = os.environ.get("TOE_CS_KMAX_UM", "").strip()
    cs_kmax_um = None
    if cs_kmax_raw:
        try:
            cs_kmax_um = float(cs_kmax_raw)
        except ValueError:
            cs_kmax_um = None

    return Config(
        sigma_model=sigma_model,
        sigma_f_khz=_env_float("TOE_SIGMA_F_KHZ", 0.05),
        sigma_k_um=_env_float("TOE_SIGMA_K_UM", 0.05),
        sigma_abs_floor_khz=_env_float("TOE_SIGMA_ABS_FLOOR_KHZ", 0.10),
        sigma_rel_frac=_env_float("TOE_SIGMA_REL_FRAC", 0.02),
        outlier_relerr_thresh=_env_float("TOE_OUTLIER_RELERR", 0.50),
        outlier_sigma_thresh=_env_float("TOE_OUTLIER_SIGMA", 5.0),
        cs_kmax_um=cs_kmax_um,
        cs_npts=_env_int("TOE_CS_NPTS", 6),
        cs_fit_through_origin=_env_bool("TOE_CS_THROUGH_ORIGIN", True),
    )


# ============================
# Theory: Bogoliubov dispersion
# (ħ ω)^2 = ε_k (ε_k + 2 μ),  ε_k = ħ^2 k^2 / (2m)
# Returns f = ω/(2π) in kHz
# ============================
def bogoliubov_f_over_2pi_khz(
    k_um_inv: np.ndarray,
    mu_over_h_khz: float = MU_OVER_H_KHZ,
    m_kg: float = M_RB87,
) -> np.ndarray:
    k_m_inv = k_um_inv * 1e6
    mu_hz = mu_over_h_khz * 1e3
    mu_J = H * mu_hz

    eps_k = (HB**2) * (k_m_inv**2) / (2.0 * m_kg)
    omega = np.sqrt(eps_k * (eps_k + 2.0 * mu_J)) / HB

    return (omega / (2.0 * math.pi)) / 1e3  # kHz


# ============================
# Sound speed
# IMPORTANT PATCH:
#   c_s = sqrt(mu/m)   (NOT mu/m)
# mu = h*(mu/h)
# ============================
def sound_speed_from_mu(mu_over_h_khz: float = MU_OVER_H_KHZ, m_kg: float = M_RB87) -> float:
    mu_hz = mu_over_h_khz * 1e3
    mu_J = H * mu_hz
    return math.sqrt(mu_J / m_kg)  # m/s


def low_k_sound_speed_fit(
    k_um_inv: np.ndarray,
    f_khz: np.ndarray,
    cfg: Config,
) -> Tuple[Optional[float], Optional[float], Optional[float], np.ndarray]:
    """
    Fit low-k linear relation:
        f_Hz ≈ (c_s/(2π)) * k_m_inv  (+ intercept unless forced through origin)

    Returns:
        slope_Hz_per_m, intercept_Hz, c_s_fit_m_per_s, mask_used
    """
    k = np.asarray(k_um_inv, float)
    f = np.asarray(f_khz, float)

    order = np.argsort(k)
    k_sorted = k[order]
    f_sorted = f[order]

    if cfg.cs_kmax_um is not None:
        mask_sorted = k_sorted <= cfg.cs_kmax_um
    else:
        n = max(cfg.cs_npts, 2)
        mask_sorted = np.zeros_like(k_sorted, dtype=bool)
        mask_sorted[: min(n, len(k_sorted))] = True

    if mask_sorted.sum() < 2:
        return None, None, None, np.zeros_like(k, dtype=bool)

    # Convert units: k_um^-1 -> k_m^-1, f_kHz -> f_Hz
    k_m = k_sorted[mask_sorted] * 1e6
    f_hz = f_sorted[mask_sorted] * 1e3

    if cfg.cs_fit_through_origin:
        # slope = (x·y)/(x·x), intercept = 0
        denom = float(np.dot(k_m, k_m))
        if denom == 0.0:
            return None, None, None, np.zeros_like(k, dtype=bool)
        slope = float(np.dot(k_m, f_hz)) / denom
        intercept = 0.0
    else:
        # ordinary least squares for y = a x + b
        A = np.vstack([k_m, np.ones_like(k_m)]).T
        sol, *_ = np.linalg.lstsq(A, f_hz, rcond=None)
        slope = float(sol[0])
        intercept = float(sol[1])

    c_s_fit = 2.0 * math.pi * slope  # m/s

    # Build mask back in original order
    mask_used_sorted = mask_sorted
    mask_used = np.zeros_like(k, dtype=bool)
    mask_used[order] = mask_used_sorted

    return slope, intercept, c_s_fit, mask_used


# ============================
# Sigma models
# ============================
def apply_sigma_model(df: pd.DataFrame, cfg: Config):
    k = df["k_um_inv"].to_numpy(float)
    f = df["omega_over_2pi_kHz"].to_numpy(float)

    if cfg.sigma_model == "csv":
        s_k = df.get("sigma_k_um_inv", cfg.sigma_k_um)
        s_f = df.get("sigma_omega_over_2pi_kHz", cfg.sigma_f_khz)
        return np.asarray(s_k, float), np.asarray(s_f, float)

    if cfg.sigma_model == "placeholder":
        return (
            np.full(len(df), cfg.sigma_k_um),
            np.full(len(df), cfg.sigma_f_khz),
        )

    # digitization model
    s_k = np.maximum(cfg.sigma_k_um, cfg.sigma_rel_frac * k)
    s_f = np.maximum(cfg.sigma_abs_floor_khz, cfg.sigma_rel_frac * f)
    return s_k, s_f


# ============================
# Outlier logic
# ============================
def flag_outliers(f_exp, f_th, sigma_f, cfg: Config):
    resid = f_exp - f_th
    rel_err = resid / np.where(f_th != 0, f_th, np.nan)
    z = resid / sigma_f

    outlier = (
        (np.abs(rel_err) > cfg.outlier_relerr_thresh)
        | (np.abs(z) > cfg.outlier_sigma_thresh)
    )
    return resid, rel_err, z, outlier


# ============================
# Summary writer
# ============================
def detect_digitization_floor_warning(k_um_inv: np.ndarray, f_khz: np.ndarray) -> bool:
    """
    Flags if the two lowest-k points have identical y (within exact/near-exact tolerance).
    This is a common digitization artifact / floor effect.
    """
    k = np.asarray(k_um_inv, float)
    f = np.asarray(f_khz, float)
    if len(k) < 2:
        return False
    order = np.argsort(k)
    f0 = f[order[0]]
    f1 = f[order[1]]
    return bool(np.isclose(f0, f1, rtol=0.0, atol=1e-12))


def write_summary(
    cfg: Config,
    n: int,
    chi2: float,
    chi2_red: float,
    n_out: int,
    cs_fit: Optional[float],
    cs_mu: float,
    cs_pct_diff: Optional[float],
    cs_mask_used: np.ndarray,
    digitization_floor_warning: bool,
):
    lines = [
        "EVIDENCE PACKET SUMMARY",
        "",
        f"BASE_DIR: {BASE_DIR}",
        f"μ/h = {MU_OVER_H_KHZ} kHz (caption, no free parameters)",
        "",
        "CONFIGURATION",
        f"Sigma model: {cfg.sigma_model}",
        "",
        "GOODNESS OF FIT",
        f"N = {n}",
        f"χ² = {chi2:.3g}",
        f"χ²_red = {chi2_red:.3g}",
        "",
        "OUTLIERS",
        f"Flagged points = {n_out}",
        "",
        "SOUND-SPEED CHECK (LOW-k)",
        "Model relation: c_s = sqrt(μ/m)",
        f"c_s(μ) = {cs_mu:.6g} m/s",
    ]

    if cs_fit is None or cs_pct_diff is None:
        lines += [
            "c_s,fit: unavailable (insufficient low-k points / config window too small).",
        ]
    else:
        # Report the low-k window used
        if cfg.cs_kmax_um is not None:
            window_desc = f"k <= {cfg.cs_kmax_um} μm⁻¹"
        else:
            window_desc = f"first {cfg.cs_npts} points (sorted by k)"
        n_used = int(cs_mask_used.sum())

        lines += [
            f"Fit window: {window_desc} (used {n_used} points)",
            f"c_s,fit = {cs_fit:.6g} m/s",
            f"Percent difference = {cs_pct_diff:.3g} %",
        ]

    lines += [
        "",
        "WARNINGS",
    ]
    if digitization_floor_warning:
        lines += [
            "Digitization floor warning: lowest two points share identical y.",
        ]
    else:
        lines += [
            "None.",
        ]

    lines += [
        "",
        "NOTE",
        "χ² is not physically meaningful until true experimental uncertainties replace placeholders.",
    ]

    with open(SUMMARY_OUT, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))


# ============================
# Main
# ============================
def main():
    cfg = load_config()

    df = pd.read_csv(CSV_IN)
    k = df["k_um_inv"].to_numpy(float)
    f_exp = df["omega_over_2pi_kHz"].to_numpy(float)

    sigma_k, sigma_f = apply_sigma_model(df, cfg)
    f_th = bogoliubov_f_over_2pi_khz(k)

    resid, rel_err, z, outlier = flag_outliers(f_exp, f_th, sigma_f, cfg)

    chi2 = float(np.sum((resid / sigma_f) ** 2))
    chi2_red = chi2 / max(len(df), 1)

    # Low-k sound speed fit (use experimental points; you can swap to f_th if desired)
    slope, intercept, cs_fit, cs_mask_used = low_k_sound_speed_fit(k, f_exp, cfg)
    cs_mu = sound_speed_from_mu(MU_OVER_H_KHZ, M_RB87)
    cs_pct_diff = None
    if cs_fit is not None and cs_mu != 0.0:
        cs_pct_diff = 100.0 * (cs_fit - cs_mu) / cs_mu

    digitization_floor_warning = detect_digitization_floor_warning(k, f_exp)

    # Store per-point results
    df["f_th_kHz"] = f_th
    df["resid_kHz"] = resid
    df["rel_err"] = rel_err
    df["z_score"] = z
    df["outlier"] = outlier
    df.to_csv(CSV_OUT, index=False)

    # Plot
    plt.figure()
    plt.errorbar(
        k[~outlier], f_exp[~outlier], yerr=sigma_f[~outlier],
        fmt="o", label="exp (inliers)"
    )
    if np.any(outlier):
        plt.errorbar(
            k[outlier], f_exp[outlier], yerr=sigma_f[outlier],
            fmt="s", label="exp (outliers)"
        )

    k_grid = np.linspace(k.min(), k.max(), 400)
    plt.plot(
        k_grid,
        bogoliubov_f_over_2pi_khz(k_grid),
        label=f"Bogoliubov (μ/h={MU_OVER_H_KHZ} kHz)",
    )

    plt.xlabel("k (μm⁻¹)")
    plt.ylabel("ω(k)/(2π) (kHz)")
    plt.legend()
    plt.tight_layout()
    plt.savefig(PLOT_OUT, dpi=200)

    write_summary(
        cfg=cfg,
        n=len(df),
        chi2=chi2,
        chi2_red=chi2_red,
        n_out=int(outlier.sum()),
        cs_fit=cs_fit,
        cs_mu=cs_mu,
        cs_pct_diff=cs_pct_diff,
        cs_mask_used=cs_mask_used,
        digitization_floor_warning=digitization_floor_warning,
    )

    print("=== Evidence comparison complete ===")
    print(f"N = {len(df)} | outliers = {int(outlier.sum())}")
    print(f"χ²_red = {chi2_red:.3g}")
    if cs_fit is not None and cs_pct_diff is not None:
        print(f"c_s(μ)   = {cs_mu:.6g} m/s")
        print(f"c_s,fit  = {cs_fit:.6g} m/s")
        print(f"Δ%       = {cs_pct_diff:.3g} %")
    if digitization_floor_warning:
        print("WARNING: lowest two points share identical y (digitization floor).")


if __name__ == "__main__":
    main()
