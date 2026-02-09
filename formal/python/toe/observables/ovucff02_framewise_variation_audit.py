"""OV-UCFF-02: Framewise cross-variation audit scaffold.

This module implements a deterministic, quarantine-safe numeric audit for
"framewise cross-variation" of an input matrix X with shape (n_frames, n_bins).

What it computes (bookkeeping only)
- Frame-to-frame delta energy: ||x_t - x_{t-1}||_2
- Normalized delta energy: ||x_t - x_{t-1}||_2 / (||x_{t-1}||_2 + eps)
- Framewise normalized outer-product matrix C_t = (x_t x_t^T) / (||x_t||_2^2 + eps)
  and its Frobenius difference between successive frames.

Policy / limits
- Not an empirical anchor.
- Does not assert UCFF physics; it records numeric stability/variation summaries.
- Can bind to a pinned, legacy-derived internal input artifact for re-porting.

This is intended as a low-risk port target. When a concrete legacy definition
is located, it can be pinned as an input artifact and these checks can be
tightened to match it.
"""

from __future__ import annotations

from dataclasses import asdict
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
from typing import Any

import numpy as np


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _atomic_write_text(*, path: Path, text: str) -> None:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


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
    if a.shape[1] < 1:
        raise ValueError("need at least 1 bin")
    return a


def _outer_normed(v: np.ndarray, *, eps: float) -> np.ndarray:
    v = np.asarray(v, dtype=float).ravel()
    denom = float(np.dot(v, v)) + float(eps)
    return np.outer(v, v) / denom


@dataclass(frozen=True)
class OVUCFF02FramewiseVariationReport:
    schema: str
    config_tag: str
    eps: float
    n_frames: int
    n_bins: int
    baseline_frame_energy_l2_mean: float
    delta_energy_l2_mean: float
    delta_energy_l2_max: float
    delta_energy_l2_norm_mean: float
    delta_energy_l2_norm_max: float
    cross_matrix_fro_delta_mean: float
    cross_matrix_fro_delta_max: float

    def to_jsonable_without_fingerprint(self) -> dict[str, Any]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, Any]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def ovucff02_framewise_variation_audit(
    *,
    X: np.ndarray,
    eps: float = 1e-12,
    config_tag: str = "OV-UCFF-02_framewise_variation_v1",
) -> OVUCFF02FramewiseVariationReport:
    X = _as_2d_float(X)
    if eps <= 0:
        raise ValueError("eps must be > 0")

    n_frames, n_bins = int(X.shape[0]), int(X.shape[1])

    energies = np.linalg.norm(X, axis=1)
    baseline_energy_mean = float(np.mean(energies))

    delta_l2: list[float] = []
    delta_l2_norm: list[float] = []
    cross_fro: list[float] = []

    for t in range(1, n_frames):
        prev = X[t - 1]
        cur = X[t]

        d = cur - prev
        dl2 = float(np.linalg.norm(d))
        delta_l2.append(dl2)

        denom = float(np.linalg.norm(prev)) + float(eps)
        delta_l2_norm.append(float(dl2 / denom))

        C_prev = _outer_normed(prev, eps=float(eps))
        C_cur = _outer_normed(cur, eps=float(eps))
        cross_fro.append(float(np.linalg.norm(C_cur - C_prev, ord="fro")))

    return OVUCFF02FramewiseVariationReport(
        schema="OV-UCFF-02/framewise_variation_report/v1",
        config_tag=str(config_tag),
        eps=float(eps),
        n_frames=n_frames,
        n_bins=n_bins,
        baseline_frame_energy_l2_mean=float(baseline_energy_mean),
        delta_energy_l2_mean=float(np.mean(delta_l2)),
        delta_energy_l2_max=float(np.max(delta_l2)),
        delta_energy_l2_norm_mean=float(np.mean(delta_l2_norm)),
        delta_energy_l2_norm_max=float(np.max(delta_l2_norm)),
        cross_matrix_fro_delta_mean=float(np.mean(cross_fro)),
        cross_matrix_fro_delta_max=float(np.max(cross_fro)),
    )


def default_demo_inputs() -> dict[str, np.ndarray]:
    """Return canonical demo inputs for testing and artifact generation."""

    # Constant frames (zero variation) and a small drifting pattern.
    const = np.tile(np.array([1.0, 2.0, 3.0, 4.0], dtype=float), (5, 1))

    drift = []
    base = np.array([1.0, 0.5, 0.25, 0.125], dtype=float)
    for t in range(6):
        drift.append(base * (1.0 + 0.05 * t) + 0.01 * t)
    drift = np.asarray(drift, dtype=float)

    return {"constant": const, "drift": drift}


def default_pinned_input_path() -> Path:
    """Canonical pinned input path for OV-UCFF-02.

    This is a data artifact (JSON) intended for legacy re-port traceability.
    """

    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "input"
        / "OV-UCFF-02"
        / "legacy_phase51_coherence_drift_pair_density.json"
    )


def load_pinned_input_X(*, path: Path | None = None) -> np.ndarray:
    p = default_pinned_input_path() if path is None else Path(path)
    raw = json.loads(p.read_text(encoding="utf-8"))
    X = raw.get("X")
    if not isinstance(X, list):
        raise ValueError("pinned input JSON must contain key 'X' as a 2D list")
    return _as_2d_float(np.asarray(X, dtype=float))


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-UCFF-02" / "ucff_framewise_variation.json"


def write_ovucff02_framewise_variation_artifact(*, path: Path | None = None) -> Path:
    demo = default_demo_inputs()

    rep_const = ovucff02_framewise_variation_audit(X=demo["constant"])
    rep_drift = ovucff02_framewise_variation_audit(X=demo["drift"])

    pinned_path = default_pinned_input_path()
    pinned_block: dict[str, Any] | None = None
    pinned_rep: dict[str, Any] | None = None
    if pinned_path.exists():
        Xp = load_pinned_input_X(path=pinned_path)
        pinned_block = {
            "path": pinned_path.as_posix(),
            "schema": "OV-UCFF-02/pinned_input_density_pair/v1",
            "shape": [int(Xp.shape[0]), int(Xp.shape[1])],
        }
        pinned_rep = ovucff02_framewise_variation_audit(X=Xp).to_jsonable()

    payload: dict[str, Any] = {
        "schema": "OV-UCFF-02/framewise_variation_artifact/v2",
        "notes": (
            "Bookkeeping only. Includes (a) an optional pinned, legacy-derived internal input report "
            "if present, plus (b) synthetic demo reports used for regression coverage. "
            "Not external evidence and not a UCFF physics claim."
        ),
        "pinned_input": pinned_block,
        "reports": {
            "pinned": pinned_rep,
            "demo_constant": rep_const.to_jsonable(),
            "demo_drift": rep_drift.to_jsonable(),
        },
        "demo_inputs": {
            "constant": demo["constant"].tolist(),
            "drift": demo["drift"].tolist(),
        },
    }
    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return out


def default_reference_report_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return (
        repo_root
        / "formal"
        / "python"
        / "artifacts"
        / "input"
        / "OV-UCFF-02"
        / "reference_ovucff02_pinned_report.json"
    )


def load_reference_report(*, path: Path | None = None) -> dict[str, Any]:
    p = default_reference_report_path() if path is None else Path(path)
    payload = json.loads(p.read_text(encoding="utf-8"))
    ref = payload.get("reference_report")
    if not isinstance(ref, dict):
        raise ValueError("reference report JSON must contain key 'reference_report' as an object")
    return ref


def write_reference_report_from_ovucff02(
    *,
    path: Path | None = None,
    pinned_input_path: Path | None = None,
    eps: float = 1e-12,
    tool_module: str | None = None,
    tool_source_sha256: str | None = None,
) -> Path:
    """Write a frozen OV-UCFF-02 reference report from pinned input.

    This is an internal stability anchor (bookkeeping only). It should only be
    invoked under an explicit safety gate in the front-door CLI.
    """

    out = default_reference_report_path() if path is None else Path(path)
    pin = default_pinned_input_path() if pinned_input_path is None else Path(pinned_input_path)

    raw = json.loads(pin.read_text(encoding="utf-8"))
    pin_schema = str(raw.get("schema", "OV-UCFF-02/pinned_input_density_pair/v1"))
    pin_fingerprint = raw.get("fingerprint")
    pin_sha = _sha256_json(raw)

    X = load_pinned_input_X(path=pin)
    rep = ovucff02_framewise_variation_audit(X=X, eps=float(eps)).to_jsonable()

    payload: dict[str, Any] = {
        "schema": "OV-UCFF-02/reference_report/v1",
        "notes": (
            "Internal numeric baseline for OV-UCFF-02 pinned input (no legacy baseline located). "
            "Bookkeeping only; not external evidence and does not upgrade epistemic status."
        ),
        "source": {
            "path": pin.as_posix(),
            "schema": pin_schema,
            "fingerprint": pin_fingerprint,
            "sha256_canonical_json": pin_sha,
        },
        "tool": {
            "module": tool_module,
            "source_sha256": tool_source_sha256,
        },
        "reference_report": rep,
    }
    payload["fingerprint"] = _sha256_json(payload)

    _atomic_write_text(path=out, text=json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return out
