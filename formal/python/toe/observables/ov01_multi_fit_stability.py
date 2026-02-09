"""OV-01c: multi-fit stability residual and gate.

Purpose:
- Compare the OV-01 observable for a fixed FN artifact across *multiple* DR-fit
  artifacts (e.g. DR-02a vs DR-03a vs DR-04a) derived from the same underlying
  dataset.
- Produce pairwise normalized cross-fit residuals and summary statistics
  (R_max, R_rms), plus an explicit (provisional) prune/retain decision.

This is deterministic and contains no filesystem I/O.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math

from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.observables.ov01_observable import OV01ObservableReport, ov01_observable_residual_from


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class OV01MultiFitStabilityReport:
    """Deterministic report for OV-01 multi-fit stability."""

    config_tag: str

    fn_fingerprint: str
    dr_fingerprints: tuple[str, ...]

    metric_fingerprints: tuple[str, ...]
    obs_values: tuple[float, ...]

    epsilon: float

    # Ordered as (i, j, r_ij) with i < j.
    pairwise_r: tuple[tuple[int, int, float], ...]

    r_max: float
    r_rms: float

    tau_obs: float
    retain: bool

    def fingerprint(self) -> str:
        payload = {
            "config_tag": self.config_tag,
            "fn_fingerprint": self.fn_fingerprint,
            "dr_fingerprints": list(self.dr_fingerprints),
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


def ov01_multi_fit_stability(
    fn_artifact: FN01Artifact1D,
    dr_fits: list[DR01Fit1D] | tuple[DR01Fit1D, ...],
    *,
    epsilon: float = 1.0e-12,
    tau_obs: float = 0.10,
    config_tag: str = "OV-01c_multi_fit_stability_v1",
) -> OV01MultiFitStabilityReport:
    """Compute OV-01 multi-fit stability residuals and apply a gate.

    For each DR fit i, compute the OV-01 observable value obs_i.

    Pairwise residuals:
        R_ij = |obs_i - obs_j| / max(|obs_i|, |obs_j|, epsilon)

    Summary:
        R_max = max_{i<j} R_ij
        R_rms = sqrt(mean_{i<j} R_ij^2)

    Gate (provisional):
        retain iff R_max <= tau_obs

    Notes:
    - This is designed to strengthen the cross-fit robustness check by using
      three (or more) window choices.
    """

    if epsilon <= 0.0:
        raise ValueError("epsilon must be positive")
    if tau_obs < 0.0:
        raise ValueError("tau_obs must be non-negative")

    fits = list(dr_fits)
    if len(fits) < 2:
        raise ValueError("dr_fits must contain at least 2 fits")

    reps: list[OV01ObservableReport] = [ov01_observable_residual_from(fn_artifact, dr) for dr in fits]

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

    if not pairwise:
        # Defensive: should be impossible for len(fits) >= 2.
        raise RuntimeError("No pairwise residuals computed")

    r_max = max(r for (_, _, r) in pairwise)
    r_rms = math.sqrt(sum(r * r for (_, _, r) in pairwise) / len(pairwise))

    retain = bool(r_max <= float(tau_obs))

    return OV01MultiFitStabilityReport(
        config_tag=str(config_tag),
        fn_fingerprint=fn_artifact.fingerprint(),
        dr_fingerprints=dr_fps,
        metric_fingerprints=metric_fps,
        obs_values=obs_values,
        epsilon=float(epsilon),
        pairwise_r=tuple(pairwise),
        r_max=float(r_max),
        r_rms=float(r_rms),
        tau_obs=float(tau_obs),
        retain=retain,
    )
