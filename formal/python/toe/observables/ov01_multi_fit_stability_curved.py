"""OV-01 (curved DR): multi-fit stability residual and gate.

This mirrors OV-01c/OV-01d but consumes curvature-aware DR fit artifacts.

Residuals are computed on the OV-01 observable values built from the BR-01 metric
constructed using c0 as the k->0 sound-speed proxy.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math

from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.observables.ov01_observable_curved import (
    OV01ObservableCurvedReport,
    ov01_observable_residual_from_curved,
)


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class OV01MultiFitStabilityCurvedReport:
    config_tag: str

    fn_fingerprint: str
    dr_curved_fingerprints: tuple[str, ...]

    metric_fingerprints: tuple[str, ...]
    obs_values: tuple[float, ...]

    epsilon: float
    pairwise_r: tuple[tuple[int, int, float], ...]

    r_max: float
    r_rms: float

    tau_obs: float
    retain: bool

    def fingerprint(self) -> str:
        payload = {
            "config_tag": self.config_tag,
            "fn_fingerprint": self.fn_fingerprint,
            "dr_curved_fingerprints": list(self.dr_curved_fingerprints),
            "metric_fingerprints": list(self.metric_fingerprints),
            "obs_values": [float(x) for x in self.obs_values],
            "epsilon": float(self.epsilon),
            "pairwise_r": [[int(i), int(j), float(r)] for (i, j, r) in self.pairwise_r],
            "r_max": float(self.r_max),
            "r_rms": float(self.r_rms),
            "tau_obs": float(self.tau_obs),
            "retain": bool(self.retain),
        }
        return _sha256_json(payload)


def ov01_multi_fit_stability_curved(
    fn_artifact: FN01Artifact1D,
    dr_fits_curved: list[DR01FitCurved1D] | tuple[DR01FitCurved1D, ...],
    *,
    epsilon: float = 1.0e-12,
    tau_obs: float = 0.10,
    config_tag: str = "OV-01_multi_fit_stability_curved_v1",
) -> OV01MultiFitStabilityCurvedReport:
    if epsilon <= 0.0:
        raise ValueError("epsilon must be positive")
    if tau_obs < 0.0:
        raise ValueError("tau_obs must be non-negative")

    fits = list(dr_fits_curved)
    if len(fits) < 2:
        raise ValueError("dr_fits_curved must contain at least 2 fits")

    reps: list[OV01ObservableCurvedReport] = [ov01_observable_residual_from_curved(fn_artifact, dr) for dr in fits]

    obs_values = tuple(float(r.obs_value) for r in reps)
    metric_fps = tuple(str(r.metric_fingerprint) for r in reps)
    dr_fps = tuple(dr.fingerprint() for dr in fits)

    pairwise: list[tuple[int, int, float]] = []
    for i in range(len(fits)):
        for j in range(i + 1, len(fits)):
            oi = float(obs_values[i])
            oj = float(obs_values[j])
            denom = max(abs(oi), abs(oj), float(epsilon))
            rij = abs(oi - oj) / denom
            pairwise.append((i, j, float(rij)))

    r_max = max(r for (_, _, r) in pairwise)
    r_rms = math.sqrt(sum(r * r for (_, _, r) in pairwise) / len(pairwise))

    retain = bool(r_max <= float(tau_obs))

    return OV01MultiFitStabilityCurvedReport(
        config_tag=str(config_tag),
        fn_fingerprint=fn_artifact.fingerprint(),
        dr_curved_fingerprints=dr_fps,
        metric_fingerprints=metric_fps,
        obs_values=obs_values,
        epsilon=float(epsilon),
        pairwise_r=tuple(pairwise),
        r_max=float(r_max),
        r_rms=float(r_rms),
        tau_obs=float(tau_obs),
        retain=retain,
    )
