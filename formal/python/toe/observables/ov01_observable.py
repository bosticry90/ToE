"""OV-01: minimal FN-dependent observable residual.

This is intentionally a small, deterministic observable that depends on:
- an FN artifact (parameterization), and
- a BR-01/MT-01 metric produced from a DR-01 fit artifact.

Option A (consistency residual): target is 0 and residual is |obs_value|.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json

import numpy as np

from formal.python.toe.bridges.br01_dispersion_to_metric import br01_metric_from_DR01_fit
from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit import DR01Fit1D


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _first_scalar(x: np.ndarray) -> float:
    return float(np.asarray(x).ravel()[0])


def _metric_scalar_fingerprint(*, g_tt: float, g_tx: float, g_xx: float, c_s2: float) -> str:
    return _sha256_json({"g_tt": float(g_tt), "g_tx": float(g_tx), "g_xx": float(g_xx), "c_s2": float(c_s2)})


@dataclass(frozen=True)
class OV01ObservableReport:
    """Deterministic report for OV-01 observable and residual."""

    config_tag: str

    fn_fingerprint: str
    dr_fingerprint: str
    metric_fingerprint: str

    # Scalars extracted from the BR-01/MT-01 metric (constant-field in current use).
    g_tt: float
    g_tx: float
    g_xx: float
    c_s2: float

    # FN parameterization
    g_param: float

    # Observable and residual
    obs_value: float
    target_value: float
    residual: float

    def fingerprint(self) -> str:
        payload = {
            "config_tag": self.config_tag,
            "fn_fingerprint": self.fn_fingerprint,
            "dr_fingerprint": self.dr_fingerprint,
            "metric_fingerprint": self.metric_fingerprint,
            "g_tt": float(self.g_tt),
            "g_tx": float(self.g_tx),
            "g_xx": float(self.g_xx),
            "c_s2": float(self.c_s2),
            "g_param": float(self.g_param),
            "obs_value": float(self.obs_value),
            "target_value": float(self.target_value),
            "residual": float(self.residual),
        }
        return _sha256_json(payload)


def ov01_observable_residual_from(
    fn_artifact: FN01Artifact1D,
    dr_fit_artifact: DR01Fit1D,
    *,
    config_tag: str = "OV-01_consistency_v1",
) -> OV01ObservableReport:
    """Compute OV-01 observable and residual.

    Definition (Option A, consistency residual):

        obs_value = g * c_s2
        target_value = 0
        residual = |obs_value|

    where c_s2 is extracted from the BR-01/MT-01 metric constructed from the
    DR fit artifact in the current BR-01 unit-density gauge.

    This is probe-relative and intentionally minimal: it forces the pipeline to
    propagate an FN parameter into an observable computed from the data-backed
    DR → metric path.
    """

    params = fn_artifact.params_dict()
    if "g" not in params:
        raise ValueError("OV-01 requires FN param 'g'")

    g_param = float(params["g"])

    metric = br01_metric_from_DR01_fit(dr_fit_artifact, n=1)

    g_tt = _first_scalar(metric.g_tt)
    g_tx = _first_scalar(metric.g_tx)
    g_xx = _first_scalar(metric.g_xx)
    c_s2 = _first_scalar(metric.c_s2)

    metric_fp = _metric_scalar_fingerprint(g_tt=g_tt, g_tx=g_tx, g_xx=g_xx, c_s2=c_s2)

    obs_value = float(g_param * c_s2)
    target_value = 0.0
    residual = float(abs(obs_value))

    return OV01ObservableReport(
        config_tag=str(config_tag),
        fn_fingerprint=fn_artifact.fingerprint(),
        dr_fingerprint=dr_fit_artifact.fingerprint(),
        metric_fingerprint=metric_fp,
        g_tt=float(g_tt),
        g_tx=float(g_tx),
        g_xx=float(g_xx),
        c_s2=float(c_s2),
        g_param=float(g_param),
        obs_value=obs_value,
        target_value=target_value,
        residual=residual,
    )
