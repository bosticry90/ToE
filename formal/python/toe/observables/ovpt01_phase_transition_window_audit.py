"""OV-PT-01: Phase transition window detector (hexatic-style scaffold).

This module provides a small, deterministic detector for a two-step transition
pattern typical of 2D hexatic melting:
- translational order drops at T1,
- orientational order drops later at T2 > T1,
- leaving a window (T1, T2) with orientational order present but translational
  order absent.

This does not simulate melting; it audits *whether a provided dataset* exhibits
this pattern.
"""

from __future__ import annotations

from dataclasses import dataclass
from dataclasses import asdict
import hashlib
import json
from pathlib import Path

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


@dataclass(frozen=True)
class OVPT01HexaticWindowReport:
    schema: str
    config_tag: str
    orient_threshold: float
    transl_threshold: float
    n_samples: int
    has_hexatic_window: bool
    window_T_low: float | None
    window_T_high: float | None

    def to_jsonable_without_fingerprint(self) -> dict[str, object]:
        return asdict(self)

    def fingerprint(self) -> str:
        return _sha256_json(self.to_jsonable_without_fingerprint())

    def to_jsonable(self) -> dict[str, object]:
        d = dict(self.to_jsonable_without_fingerprint())
        d["fingerprint"] = self.fingerprint()
        return d


def _as_1d_float(x: np.ndarray) -> np.ndarray:
    a = np.asarray(x, dtype=float).ravel()
    return a


def ovpt01_detect_hexatic_window(
    *,
    T: np.ndarray,
    transl_order: np.ndarray,
    orient_order: np.ndarray,
    transl_threshold: float = 0.3,
    orient_threshold: float = 0.6,
    config_tag: str = "OV-PT-01_hexatic_window_v1",
) -> OVPT01HexaticWindowReport:
    """Detect whether there exists a temperature window consistent with hexatic order."""

    T = _as_1d_float(T)
    transl_order = _as_1d_float(transl_order)
    orient_order = _as_1d_float(orient_order)

    if not (len(T) == len(transl_order) == len(orient_order)):
        raise ValueError("T, transl_order, orient_order must have same length")
    if len(T) < 3:
        raise ValueError("need at least 3 samples")

    # Sort by temperature to make the detector ordering-robust.
    idx = np.argsort(T)
    T = T[idx]
    transl_order = transl_order[idx]
    orient_order = orient_order[idx]

    transl_is_low = transl_order <= float(transl_threshold)
    orient_is_high = orient_order >= float(orient_threshold)

    mask = np.logical_and(transl_is_low, orient_is_high)

    if not np.any(mask):
        return OVPT01HexaticWindowReport(
            schema="OV-PT-01/hexatic_window_report/v1",
            config_tag=str(config_tag),
            orient_threshold=float(orient_threshold),
            transl_threshold=float(transl_threshold),
            n_samples=int(len(T)),
            has_hexatic_window=False,
            window_T_low=None,
            window_T_high=None,
        )

    # Find the largest contiguous window in sorted temperature space.
    # (We treat contiguity in index-space as sufficient for this audit scaffold.)
    best_start = None
    best_end = None
    start = None
    for i, ok in enumerate(mask):
        if ok and start is None:
            start = i
        if (not ok) and start is not None:
            end = i - 1
            if best_start is None or (end - start) > (best_end - best_start):
                best_start, best_end = start, end
            start = None
    if start is not None:
        end = len(mask) - 1
        if best_start is None or (end - start) > (best_end - best_start):
            best_start, best_end = start, end

    assert best_start is not None and best_end is not None

    return OVPT01HexaticWindowReport(
        schema="OV-PT-01/hexatic_window_report/v1",
        config_tag=str(config_tag),
        orient_threshold=float(orient_threshold),
        transl_threshold=float(transl_threshold),
        n_samples=int(len(T)),
        has_hexatic_window=True,
        window_T_low=float(T[best_start]),
        window_T_high=float(T[best_end]),
    )


def default_artifact_path() -> Path:
    repo_root = _find_repo_root(Path(__file__))
    return repo_root / "formal" / "python" / "artifacts" / "diagnostics" / "OV-PT-01" / "hexatic_window_demo.json"


def write_ovpt01_hexatic_window_demo_artifact(*, path: Path | None = None) -> Path:
    """Write a canonical *demo* artifact using a synthetic two-step transition curve."""

    T = np.linspace(0.0, 1.0, 21)
    transl = np.where(T < 0.4, 0.9, 0.1)
    orient = np.where(T < 0.7, 0.9, 0.2)

    rep = ovpt01_detect_hexatic_window(T=T, transl_order=transl, orient_order=orient)

    payload = {
        "schema": "OV-PT-01/hexatic_window_demo_artifact/v1",
        "notes": "Synthetic demo curve only; not an external anchor and not a simulation claim.",
        "input": {
            "T": [float(x) for x in T.tolist()],
            "transl_order": [float(x) for x in transl.tolist()],
            "orient_order": [float(x) for x in orient.tolist()],
        },
        "report": rep.to_jsonable(),
    }
    payload["fingerprint"] = _sha256_json(payload)

    out = default_artifact_path() if path is None else Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    return out
