from __future__ import annotations

import csv
import hashlib
import json
import math
from pathlib import Path

import numpy as np

from formal.python.toe.comparators.ct09_independent_external_anchor_sound_speed_v0 import (
    CT09IndependentAnchorCase,
    CT09IndependentAnchorReport,
    ct09_v0_tolerances,
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
    return repo_root / "formal" / "external_evidence" / "ct09_independent_sound_speed_domain_01"


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _load_pinned_distance_time_dataset(csv_path: Path) -> tuple[np.ndarray, np.ndarray, str]:
    text = csv_path.read_text(encoding="utf-8")
    csv_sha = _sha256_text(text)

    rows: list[tuple[float, float]] = []
    with csv_path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        expected = ["time_ms", "distance_um"]
        if reader.fieldnames != expected:
            raise ValueError(f"Unexpected CT-09 CSV columns: {reader.fieldnames} (expected {expected})")

        for row in reader:
            t = float(row["time_ms"])
            d = float(row["distance_um"])
            if not (math.isfinite(t) and math.isfinite(d)):
                continue
            rows.append((t, d))

    if len(rows) < 3:
        raise ValueError("CT-09 requires at least 3 finite rows.")

    rows_sorted = sorted(rows, key=lambda r: r[0])
    time_ms = np.asarray([r[0] for r in rows_sorted], dtype=float)
    distance_um = np.asarray([r[1] for r in rows_sorted], dtype=float)
    return time_ms, distance_um, csv_sha


def _fit_linear_sound_speed(time_ms: np.ndarray, distance_um: np.ndarray) -> tuple[float, float]:
    x = np.stack([time_ms, np.ones_like(time_ms)], axis=1)
    coef, _, _, _ = np.linalg.lstsq(x, distance_um, rcond=None)
    c_um_per_ms = float(coef[0])
    intercept_um = float(coef[1])
    return c_um_per_ms, intercept_um


def _predict_distance(time_ms: np.ndarray, *, c_um_per_ms: float, intercept_um: float) -> np.ndarray:
    return c_um_per_ms * time_ms + intercept_um


def _metrics(
    distance_emp_um: np.ndarray,
    distance_pred_um: np.ndarray,
    *,
    sigma_distance_um: float,
    dof: int,
) -> tuple[float, float, float]:
    residual = distance_pred_um - distance_emp_um
    rmse = float(np.sqrt(np.mean(residual**2)))
    max_abs_error = float(np.max(np.abs(residual)))
    chi2 = float(np.sum((residual / float(sigma_distance_um)) ** 2))
    reduced_chi2 = float(chi2 / float(max(dof, 1)))
    return rmse, max_abs_error, reduced_chi2


def build_ct09_reports(
    *,
    tolerance_profile: str = "pinned",
    c_scale_negative: float = 0.5,
    sigma_distance_um: float = 20.0,
) -> tuple[CT09IndependentAnchorReport, CT09IndependentAnchorReport]:
    tolerances = ct09_v0_tolerances(tolerance_profile)
    repo_root = _find_repo_root(Path(__file__))
    artifact_dir = _default_artifact_dir(repo_root)
    dataset_csv = artifact_dir / "distance_vs_time_um_ms.csv"

    time_ms, distance_um, csv_sha = _load_pinned_distance_time_dataset(dataset_csv)

    c_fit, intercept_fit = _fit_linear_sound_speed(time_ms, distance_um)
    distance_fit = _predict_distance(time_ms, c_um_per_ms=c_fit, intercept_um=intercept_fit)
    positive_rmse, positive_max_abs, positive_red_chi2 = _metrics(
        distance_um,
        distance_fit,
        sigma_distance_um=float(sigma_distance_um),
        dof=int(time_ms.size) - 2,
    )

    c_negative = float(c_fit) * float(c_scale_negative)
    distance_negative = _predict_distance(time_ms, c_um_per_ms=c_negative, intercept_um=intercept_fit)
    negative_rmse, negative_max_abs, negative_red_chi2 = _metrics(
        distance_um,
        distance_negative,
        sigma_distance_um=float(sigma_distance_um),
        dof=int(time_ms.size) - 2,
    )

    params: dict[str, float | str] = {
        "dataset_id": "Andrews1997_Fig2_DistanceTime_Digitized_v1",
        "dataset_csv_relpath": "formal/external_evidence/ct09_independent_sound_speed_domain_01/distance_vs_time_um_ms.csv",
        "dataset_csv_sha256": str(csv_sha),
        "preprocessing_tag": "finite_filter_plus_time_sort_no_unit_conversion",
        "observable_id": "distance_um_vs_time_ms",
        "fit_model": "distance_um=c*time_ms+intercept_um",
        "c_scale_negative": float(c_scale_negative),
        "sigma_distance_um": float(sigma_distance_um),
        "eps_rmse_um": float(tolerances["eps_rmse_um"]),
        "eps_max_abs_error_um": float(tolerances["eps_max_abs_error_um"]),
        "eps_reduced_chi2": float(tolerances["eps_reduced_chi2"]),
    }

    report = CT09IndependentAnchorReport(
        schema="CT-09/independent_external_anchor_sound_speed_front_door_report/v1",
        config_tag="ct09_independent_external_anchor_sound_speed_v0",
        regime_tag="CT09_Independent_External_Anchor_Sound_Speed",
        domain_tag="ct09_independent_sound_speed_domain_01",
        params=params,
        boundary="digitized_distance_time_curve",
        cases=[
            CT09IndependentAnchorCase(
                case_id="POSITIVE",
                kind="positive_control",
                model_tag="linear_speed_fit",
                c_um_per_ms=float(c_fit),
                intercept_um=float(intercept_fit),
                rmse_um=float(positive_rmse),
                max_abs_error_um=float(positive_max_abs),
                reduced_chi2=float(positive_red_chi2),
                n_points=int(time_ms.size),
            ),
            CT09IndependentAnchorCase(
                case_id="NEGATIVE",
                kind="negative_control_model_break",
                model_tag="linear_speed_scaled",
                c_um_per_ms=float(c_negative),
                intercept_um=float(intercept_fit),
                rmse_um=float(negative_rmse),
                max_abs_error_um=float(negative_max_abs),
                reduced_chi2=float(negative_red_chi2),
                n_points=int(time_ms.size),
            ),
        ],
    )

    return report, report


def main() -> None:
    repo_root = _find_repo_root(Path(__file__))
    out_dir = _default_artifact_dir(repo_root)
    report, candidate = build_ct09_reports()
    out_dir.mkdir(parents=True, exist_ok=True)

    (out_dir / "ct09_reference_report.json").write_text(
        json.dumps(report.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )
    (out_dir / "ct09_candidate_report.json").write_text(
        json.dumps(candidate.to_jsonable(), indent=2, sort_keys=True), encoding="utf-8"
    )


if __name__ == "__main__":
    main()
