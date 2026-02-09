"""OV-01b: cross-fit stability residual and gate.

Purpose:
- Compare the OV-01 observable for a fixed FN artifact across two DR-fit artifacts
  (e.g. DR-02a vs DR-03a) derived from the same underlying dataset.
- Produce a normalized cross-fit residual and an explicit (provisional) prune/
  retain decision.

This is deterministic and contains no filesystem I/O.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json

from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.observables.ov01_observable import OV01ObservableReport, ov01_observable_residual_from


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class OV01CrossFitStabilityReport:
    """Deterministic report for OV-01 cross-fit stability."""

    config_tag: str

    fn_fingerprint: str
    dr02_fingerprint: str
    dr03_fingerprint: str

    metric02_fingerprint: str
    metric03_fingerprint: str

    obs_02: float
    obs_03: float

    epsilon: float
    r_obs_cross: float

    tau_obs: float
    retain: bool

    def fingerprint(self) -> str:
        payload = {
            "config_tag": self.config_tag,
            "fn_fingerprint": self.fn_fingerprint,
            "dr02_fingerprint": self.dr02_fingerprint,
            "dr03_fingerprint": self.dr03_fingerprint,
            "metric02_fingerprint": self.metric02_fingerprint,
            "metric03_fingerprint": self.metric03_fingerprint,
            "obs_02": float(self.obs_02),
            "obs_03": float(self.obs_03),
            "epsilon": float(self.epsilon),
            "r_obs_cross": float(self.r_obs_cross),
            "tau_obs": float(self.tau_obs),
            "retain": bool(self.retain),
        }
        return _sha256_json(payload)


def ov01_cross_fit_stability(
    fn_artifact: FN01Artifact1D,
    dr02_fit_artifact: DR01Fit1D,
    dr03_fit_artifact: DR01Fit1D,
    *,
    epsilon: float = 1.0e-12,
    tau_obs: float = 0.10,
    config_tag: str = "OV-01b_cross_fit_stability_v1",
) -> OV01CrossFitStabilityReport:
    """Compute OV-01 cross-fit stability residual and apply a gate.

    Residual:
        R_obs_cross = |obs_02 - obs_03| / max(|obs_02|, |obs_03|, epsilon)

    Gate (provisional, Rule A):
        retain iff R_obs_cross <= tau_obs

    Notes:
    - tau_obs is intentionally provisional and exists to force an explicit
      prune/retain decision into the evidence loop.
    - obs_02/obs_03 are the OV-01 observable values (not residuals).
    """

    if epsilon <= 0.0:
        raise ValueError("epsilon must be positive")
    if tau_obs < 0.0:
        raise ValueError("tau_obs must be non-negative")

    rep_02: OV01ObservableReport = ov01_observable_residual_from(fn_artifact, dr02_fit_artifact)
    rep_03: OV01ObservableReport = ov01_observable_residual_from(fn_artifact, dr03_fit_artifact)

    obs_02 = float(rep_02.obs_value)
    obs_03 = float(rep_03.obs_value)

    denom = max(abs(obs_02), abs(obs_03), float(epsilon))
    r_obs_cross = abs(obs_02 - obs_03) / denom

    retain = bool(r_obs_cross <= float(tau_obs))

    return OV01CrossFitStabilityReport(
        config_tag=str(config_tag),
        fn_fingerprint=fn_artifact.fingerprint(),
        dr02_fingerprint=dr02_fit_artifact.fingerprint(),
        dr03_fingerprint=dr03_fit_artifact.fingerprint(),
        metric02_fingerprint=rep_02.metric_fingerprint,
        metric03_fingerprint=rep_03.metric_fingerprint,
        obs_02=obs_02,
        obs_03=obs_03,
        epsilon=float(epsilon),
        r_obs_cross=float(r_obs_cross),
        tau_obs=float(tau_obs),
        retain=retain,
    )
