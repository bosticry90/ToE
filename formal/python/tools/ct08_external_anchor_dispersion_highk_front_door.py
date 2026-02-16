from __future__ import annotations

import csv
import hashlib
import json
import math
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.ct08_external_anchor_dispersion_highk_slice_v0 import (
    CT08ExternalAnchorHighKCase,
    CT08ExternalAnchorHighKReport,
    ct08_v0_tolerances,
)


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _default_artifact_dir(repo_root: Path) -> Path:
    return repo_root / "formal" / "external_evidence" / "ct08_external_anchor_dispersion_highk_domain_01"


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _load_origin_dataset(csv_path: Path) -> tuple[np.ndarray, np.ndarray, np.ndarray, str]:
    text = csv_path.read_text(encoding="utf-8")
    csv_sha = _sha256_text(text)

    rows: list[tuple[float, float, float]] = []
    with csv_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None:
            raise ValueError("CT-08 origin CSV has no header.")
        fields = set(reader.fieldnames)
        required = {"k_um_inv", "omega_over_2pi_kHz", "sigma_omega_over_2pi_kHz"}
        if not required.issubset(fields):
            raise ValueError(f"CT-08 origin CSV missing required columns: {sorted(required - fields)}")

        for row in reader:
            k = float(row["k_um_inv"])
            omega = float(row["omega_over_2pi_kHz"])
            sigma = float(row["sigma_omega_over_2pi_kHz"])
            if not (math.isfinite(k) and math.isfinite(omega) and math.isfinite(sigma)):
                continue
            if sigma <= 0.0:
                raise ValueError("CT-08 sigma_omega_over_2pi_kHz must be > 0")
            rows.append((k, omega, sigma))

    if len(rows) < 6:
        raise ValueError("CT-08 requires at least 6 finite source rows.")

    rows_sorted = sorted(rows, key=lambda r: r[0])
    k = np.asarray([r[0] for r in rows_sorted], dtype=float)
    omega = np.asarray([r[1] for r in rows_sorted], dtype=float)
    sigma = np.asarray([r[2] for r in rows_sorted], dtype=float)
    return k, omega, sigma, csv_sha


def _apply_highk_slice(
    k_um_inv: np.ndarray,
    omega_khz: np.ndarray,
    sigma_khz: np.ndarray,
    *,
    k_quantile: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, float]:
    if not (0.0 < float(k_quantile) <= 1.0):
        raise ValueError("CT-08 k_quantile must be in (0, 1].")

    k_min = float(np.quantile(k_um_inv, float(k_quantile)))
    mask = k_um_inv >= k_min
    k_slice = k_um_inv[mask]
    omega_slice = omega_khz[mask]
    sigma_slice = sigma_khz[mask]
    if int(k_slice.size) < 6:
        raise ValueError("CT-08 high-k slice has fewer than 6 points; adjust k_quantile.")
    return k_slice, omega_slice, sigma_slice, k_min


def _fit_bogoliubov_proxy(k_um_inv: np.ndarray, omega_khz: np.ndarray) -> tuple[float, float]:
    x = np.stack([k_um_inv**2, k_um_inv**4], axis=1)
    y = omega_khz**2
    coef, _, _, _ = np.linalg.lstsq(x, y, rcond=None)
    c_s2 = max(float(coef[0]), 0.0)
    alpha = max(float(coef[1]), 0.0)
    return c_s2, alpha


def _predict_omega(k_um_inv: np.ndarray, *, c_s2: float, alpha: float) -> np.ndarray:
    omega2 = c_s2 * (k_um_inv**2) + alpha * (k_um_inv**4)
    return np.sqrt(np.maximum(omega2, 0.0))


def _metrics(omega_emp: np.ndarray, omega_pred: np.ndarray, sigma: np.ndarray, *, dof: int) -> tuple[float, float, float]:
    residual = omega_pred - omega_emp
    rmse = float(np.sqrt(np.mean(residual**2)))
    max_abs_error = float(np.max(np.abs(residual)))
    chi2 = float(np.sum((residual / sigma) ** 2))
    reduced_chi2 = float(chi2 / float(max(dof, 1)))
    return rmse, max_abs_error, reduced_chi2


def build_ct08_reports(
    *,
    tolerance_profile: str = "pinned",
    k_quantile: float = 0.5,
    alpha_scale_negative: float = 0.5,
) -> tuple[CT08ExternalAnchorHighKReport, CT08ExternalAnchorHighKReport]:
    tolerances = ct08_v0_tolerances(tolerance_profile)
    repo_root = _find_repo_root(Path(__file__))
    artifact_dir = _default_artifact_dir(repo_root)
    origin_csv = repo_root / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001" / "omega_k_data.csv"

    k_um_inv, omega_khz, sigma_khz, csv_sha = _load_origin_dataset(origin_csv)
    k_slice, omega_slice, sigma_slice, k_min_um_inv = _apply_highk_slice(
        k_um_inv,
        omega_khz,
        sigma_khz,
        k_quantile=float(k_quantile),
    )

    c_s2_fit, alpha_fit = _fit_bogoliubov_proxy(k_slice, omega_slice)
    omega_fit = _predict_omega(k_slice, c_s2=c_s2_fit, alpha=alpha_fit)
    positive_rmse, positive_max_abs, positive_red_chi2 = _metrics(
        omega_slice,
        omega_fit,
        sigma_slice,
        dof=int(k_slice.size) - 2,
    )

    alpha_negative = float(alpha_fit) * float(alpha_scale_negative)
    omega_negative = _predict_omega(k_slice, c_s2=c_s2_fit, alpha=alpha_negative)
    negative_rmse, negative_max_abs, negative_red_chi2 = _metrics(
        omega_slice,
        omega_negative,
        sigma_slice,
        dof=int(k_slice.size) - 2,
    )

    params: dict[str, float | str | bool | int] = {
        "origin_dataset_id": "Steinhauer2001_Fig3a_Digitized_v1",
        "origin_dataset_csv_relpath": "formal/external_evidence/bec_bragg_steinhauer_2001/omega_k_data.csv",
        "origin_dataset_csv_sha256": str(csv_sha),
        "preprocessing_tag": "finite_filter_plus_k_sort_plus_highk_quantile_slice",
        "observable_id": "omega_over_2pi_kHz_vs_k_um_inv",
        "fit_model": "omega2=c_s2*k^2+alpha*k^4",
        "k_quantile": float(k_quantile),
        "k_min_um_inv": float(k_min_um_inv),
        "n_slice_points": int(k_slice.size),
        "alpha_scale_negative": float(alpha_scale_negative),
        "eps_rmse_kHz": float(tolerances["eps_rmse_kHz"]),
        "eps_max_abs_error_kHz": float(tolerances["eps_max_abs_error_kHz"]),
        "eps_reduced_chi2": float(tolerances["eps_reduced_chi2"]),
        "non_independent_of_ct06": True,
    }

    report = CT08ExternalAnchorHighKReport(
        schema="CT-08/external_anchor_dispersion_highk_front_door_report/v1",
        config_tag="ct08_external_anchor_dispersion_highk_slice_v0",
        regime_tag="CT08_External_Anchor_Dispersion_HighK_Slice",
        domain_tag="ct08_external_anchor_dispersion_highk_domain_01",
        params=params,
        boundary="digitized_dispersion_highk_slice",
        cases=[
            CT08ExternalAnchorHighKCase(
                case_id="POSITIVE",
                kind="positive_control",
                model_tag="bogoliubov_proxy_fit_highk_slice",
                c_s2_kHz2_um2=float(c_s2_fit),
                alpha_kHz2_um4=float(alpha_fit),
                alpha_scale=1.0,
                rmse_kHz=float(positive_rmse),
                max_abs_error_kHz=float(positive_max_abs),
                reduced_chi2=float(positive_red_chi2),
                n_points=int(k_slice.size),
            ),
            CT08ExternalAnchorHighKCase(
                case_id="NEGATIVE",
                kind="negative_control_model_break",
                model_tag="bogoliubov_proxy_alpha_scaled_highk_slice",
                c_s2_kHz2_um2=float(c_s2_fit),
                alpha_kHz2_um4=float(alpha_negative),
                alpha_scale=float(alpha_scale_negative),
                rmse_kHz=float(negative_rmse),
                max_abs_error_kHz=float(negative_max_abs),
                reduced_chi2=float(negative_red_chi2),
                n_points=int(k_slice.size),
            ),
        ],
    )

    _ = artifact_dir
    return report, report


def main() -> None:
    repo_root = _find_repo_root(Path(__file__))
    out_dir = _default_artifact_dir(repo_root)
    report, candidate = build_ct08_reports()
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "ct08_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "ct08_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
