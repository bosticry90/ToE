"""OV-01g: fit-family robustness gate (linear vs curved DR).

Purpose:
- Convert the empirical observation "curved reduces multi-window spread" into an
    explicit, decision-grade gate.
- Compare the OV-01 multi-window envelope for two DR-fit families over the same
    underlying window samples: (linear-through-origin) vs (curvature-aware proxy).

Key interpretation guardrail:
- "prefer_curved" is an operational robustness decision (reduced sensitivity to
    window choice / linearization brittleness). It is not a claim that the proxy
    curvature parameter beta is nonzero or physically inferred.

Data hygiene:
- Window lists are deduplicated by data_fingerprint before computing envelopes,
    so identical frozen samples (aliases under digitization) are not double-counted.

This is deterministic and contains no filesystem I/O.

Gate policy (provisional):
- Compute R_max_linear, R_max_curved.
- Define Q = R_max_curved / R_max_linear.
- Prefer curved iff (Q <= q_threshold) AND curved fit-quality is admissible.
- Otherwise: robustness_failed (downstream must treat OV-based pruning as
    non-decisive for family selection).

Fit-quality admissibility is evaluated on the curved artifacts only, using
explicit, conservative thresholds on y=omega/k diagnostics.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math

from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit_adequacy import dr01_check_curved_fit_adequacy
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.observables.ov01_multi_fit_stability import OV01MultiFitStabilityReport, ov01_multi_fit_stability
from formal.python.toe.observables.ov01_multi_fit_stability_curved import (
    OV01MultiFitStabilityCurvedReport,
    ov01_multi_fit_stability_curved,
)


def ov01_fit_family_robustness_failure_reasons(report: OV01FitFamilyRobustnessReport) -> list[str]:
    """Return deterministic, policy-defined reasons for robustness failure.

    This is intentionally non-interpretive and derived only from the report
    fields used by the OV-01 family-selection policy.
    """

    reasons: list[str] = []

    # Degenerate baseline: cannot form a meaningful ratio.
    if float(report.r_max_linear) == 0.0:
        reasons.append("r_max_linear_zero")

    # Curved adequacy is a hard requirement for selecting curved.
    if not bool(report.curved_adequacy_passes):
        reasons.append("curved_adequacy_failed")

    # Window-stability ratio gate.
    if (not math.isnan(float(report.q_ratio))) and (float(report.q_ratio) > float(report.q_threshold)):
        reasons.append("q_ratio_above_threshold")

    # Fallback: if robustness_failed but no specific clause triggers, disclose that
    # selection was non-decisive under the current policy.
    if bool(report.robustness_failed) and (not reasons):
        reasons.append("policy_non_prefer")

    return reasons


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _dedupe_aligned_windows(
    dr_fits_linear: list[DR01Fit1D] | tuple[DR01Fit1D, ...],
    dr_fits_curved: list[DR01FitCurved1D] | tuple[DR01FitCurved1D, ...],
) -> tuple[list[DR01Fit1D], list[DR01FitCurved1D]]:
    """Deduplicate aligned linear/curved window lists by underlying data.

    This prevents double-counting if two window IDs happen to select the same
    frozen sample under digitization (same data_fingerprint).
    """

    if len(dr_fits_linear) != len(dr_fits_curved):
        raise ValueError("dr_fits_linear and dr_fits_curved must have the same length")

    seen: set[str] = set()
    lin_out: list[DR01Fit1D] = []
    curv_out: list[DR01FitCurved1D] = []

    for lin, curv in zip(list(dr_fits_linear), list(dr_fits_curved), strict=True):
        if (
            lin.data_fingerprint is not None
            and curv.data_fingerprint is not None
            and lin.data_fingerprint != curv.data_fingerprint
        ):
            raise ValueError("Linear/curved DR window fingerprints do not match")

        dfp = curv.data_fingerprint or lin.data_fingerprint

        # Fallback: if fingerprints are missing, treat as unique (do not dedupe).
        if dfp is None:
            dfp = f"none:{lin.fingerprint()}::{curv.fingerprint()}"

        if dfp in seen:
            continue
        seen.add(dfp)
        lin_out.append(lin)
        curv_out.append(curv)

    return lin_out, curv_out


@dataclass(frozen=True)
class OV01FitFamilyRobustnessReport:
    config_tag: str

    adequacy_policy: str

    fn_fingerprint: str

    linear_report_fingerprint: str
    curved_report_fingerprint: str

    r_max_linear: float
    r_rms_linear: float

    r_max_curved: float
    r_rms_curved: float

    q_ratio: float
    q_threshold: float

    curved_adequacy_passes: bool

    prefer_curved: bool
    robustness_failed: bool

    def fingerprint(self) -> str:
        payload = {
            "config_tag": self.config_tag,
            "adequacy_policy": str(self.adequacy_policy),
            "fn_fingerprint": self.fn_fingerprint,
            "linear_report_fingerprint": self.linear_report_fingerprint,
            "curved_report_fingerprint": self.curved_report_fingerprint,
            "r_max_linear": float(self.r_max_linear),
            "r_rms_linear": float(self.r_rms_linear),
            "r_max_curved": float(self.r_max_curved),
            "r_rms_curved": float(self.r_rms_curved),
            "q_ratio": float(self.q_ratio),
            "q_threshold": float(self.q_threshold),
            "curved_adequacy_passes": bool(self.curved_adequacy_passes),
            "prefer_curved": bool(self.prefer_curved),
            "robustness_failed": bool(self.robustness_failed),
        }
        return _sha256_json(payload)


def ov01_fit_family_robustness_gate(
    fn_artifact: FN01Artifact1D,
    dr_fits_linear: list[DR01Fit1D] | tuple[DR01Fit1D, ...],
    dr_fits_curved: list[DR01FitCurved1D] | tuple[DR01FitCurved1D, ...],
    *,
    epsilon: float = 1.0e-12,
    tau_obs: float = 0.10,
    q_threshold: float = 0.90,
    adequacy_policy: str = "DQ-01_v1",
    config_tag: str = "OV-01g_fit_family_robustness_v1",
) -> OV01FitFamilyRobustnessReport:
    if epsilon <= 0.0:
        raise ValueError("epsilon must be positive")
    if tau_obs < 0.0:
        raise ValueError("tau_obs must be non-negative")
    if q_threshold <= 0.0:
        raise ValueError("q_threshold must be positive")

    dr_fits_linear_dedup, dr_fits_curved_dedup = _dedupe_aligned_windows(dr_fits_linear, dr_fits_curved)

    rep_lin: OV01MultiFitStabilityReport = ov01_multi_fit_stability(
        fn_artifact,
        list(dr_fits_linear_dedup),
        epsilon=float(epsilon),
        tau_obs=float(tau_obs),
        config_tag="OV-01g_linear_family_envelope",
    )

    rep_curv: OV01MultiFitStabilityCurvedReport = ov01_multi_fit_stability_curved(
        fn_artifact,
        list(dr_fits_curved_dedup),
        epsilon=float(epsilon),
        tau_obs=float(tau_obs),
        config_tag="OV-01g_curved_family_envelope",
    )

    r_max_linear = float(rep_lin.r_max)
    r_max_curved = float(rep_curv.r_max)

    if r_max_linear == 0.0:
        q_ratio = float("nan")
    else:
        q_ratio = float(r_max_curved / r_max_linear)

    curved_adequacy_passes = all(
        dr01_check_curved_fit_adequacy(dr, policy=str(adequacy_policy)).passes for dr in list(dr_fits_curved_dedup)
    )

    prefer_curved = bool(curved_adequacy_passes and (not math.isnan(q_ratio)) and (q_ratio <= float(q_threshold)))

    # If we cannot confidently select curved under the provisional rule, treat
    # the situation as a robustness failure for family-selection purposes.
    robustness_failed = bool(not prefer_curved)

    return OV01FitFamilyRobustnessReport(
        config_tag=str(config_tag),
        adequacy_policy=str(adequacy_policy),
        fn_fingerprint=fn_artifact.fingerprint(),
        linear_report_fingerprint=rep_lin.fingerprint(),
        curved_report_fingerprint=rep_curv.fingerprint(),
        r_max_linear=r_max_linear,
        r_rms_linear=float(rep_lin.r_rms),
        r_max_curved=r_max_curved,
        r_rms_curved=float(rep_curv.r_rms),
        q_ratio=float(q_ratio),
        q_threshold=float(q_threshold),
        curved_adequacy_passes=bool(curved_adequacy_passes),
        prefer_curved=bool(prefer_curved),
        robustness_failed=bool(robustness_failed),
    )
