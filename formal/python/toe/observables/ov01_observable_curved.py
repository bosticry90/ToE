"""OV-01 (curved DR): minimal FN-dependent observable residual.

This mirrors OV-01 but consumes a curvature-aware DR fit artifact.

Observable definition is unchanged (Option A):

    obs_value = g * c_s2

where c_s2 is extracted from the BR-01/MT-01 metric constructed from the curved
DR fit artifact using c0 as the k->0 sound-speed proxy.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json

import numpy as np

from formal.python.toe.bridges.br01_dispersion_to_metric import br01_metric_from_DR01_fit_curved
from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _first_scalar(x: np.ndarray) -> float:
    return float(np.asarray(x).ravel()[0])


def _metric_scalar_fingerprint(*, g_tt: float, g_tx: float, g_xx: float, c_s2: float) -> str:
    return _sha256_json({"g_tt": float(g_tt), "g_tx": float(g_tx), "g_xx": float(g_xx), "c_s2": float(c_s2)})


@dataclass(frozen=True)
class OV01ObservableCurvedReport:
    config_tag: str

    fn_fingerprint: str
    dr_curved_fingerprint: str
    metric_fingerprint: str

    g_tt: float
    g_tx: float
    g_xx: float
    c_s2: float

    g_param: float

    obs_value: float
    target_value: float
    residual: float

    def fingerprint(self) -> str:
        payload = {
            "config_tag": self.config_tag,
            "fn_fingerprint": self.fn_fingerprint,
            "dr_curved_fingerprint": self.dr_curved_fingerprint,
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


def ov01_observable_residual_from_curved(
    fn_artifact: FN01Artifact1D,
    dr_fit_artifact_curved: DR01FitCurved1D,
    *,
    config_tag: str = "OV-01_consistency_curved_v1",
) -> OV01ObservableCurvedReport:
    params = fn_artifact.params_dict()
    if "g" not in params:
        raise ValueError("OV-01 requires FN param 'g'")

    g_param = float(params["g"])

    metric = br01_metric_from_DR01_fit_curved(dr_fit_artifact_curved, n=1)

    g_tt = _first_scalar(metric.g_tt)
    g_tx = _first_scalar(metric.g_tx)
    g_xx = _first_scalar(metric.g_xx)
    c_s2 = _first_scalar(metric.c_s2)

    metric_fp = _metric_scalar_fingerprint(g_tt=g_tt, g_tx=g_tx, g_xx=g_xx, c_s2=c_s2)

    obs_value = float(g_param * c_s2)
    target_value = 0.0
    residual = float(abs(obs_value))

    return OV01ObservableCurvedReport(
        config_tag=str(config_tag),
        fn_fingerprint=fn_artifact.fingerprint(),
        dr_curved_fingerprint=dr_fit_artifact_curved.fingerprint(),
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
