"""DQ-01: DR-01 fit adequacy gate (curved proxy).

Purpose:
- Provide a deterministic, decision-grade adequacy check for curvature-aware
  DR-01 fit artifacts (`DR01FitCurved1D`).
- Avoid using R^2(y) as a required check (it can be misleading in y=omega/k
  space when y varies weakly around its mean).

This module contains no filesystem I/O.

Default thresholds are conservative but intentionally not brittle; they are
intended to be tightened as the science loop progresses.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import math

from formal.python.toe.dr01_fit_curved import DR01FitCurved1D


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


@dataclass(frozen=True)
class DR01FitAdequacy1D:
    """Deterministic adequacy report for a single curved DR fit artifact."""

    passes: bool
    reason_codes: tuple[str, ...]

    metrics: dict[str, float]

    input_fingerprint: str

    def fingerprint(self) -> str:
        payload = {
            "passes": bool(self.passes),
            "reason_codes": list(self.reason_codes),
            "metrics": {k: float(v) for (k, v) in sorted(self.metrics.items())},
            "input_fingerprint": str(self.input_fingerprint),
        }
        return _sha256_json(payload)


def dr01_check_curved_fit_adequacy(
    fit: DR01FitCurved1D,
    *,
    policy: str = "DQ-01_v1",
    n_points_min: int = 5,
    rmse_omega_over_k_max_m_per_s: float = 4.0e-4,
    c0_stderr_max_m_per_s: float = 3.0e-4,
    # Tiered low-N handling (DQ-01_v2 only): allow N==4 if RMSE and c0 stderr
    # pass stricter thresholds; ignore beta identifiability at N==4.
    rmse_omega_over_k_max_m_per_s_strict_4pt: float = 2.5e-4,
    c0_stderr_max_m_per_s_strict_4pt: float = 2.8e-4,
    # Curvature identifiability: require either a detectable beta (SNR) OR
    # sufficiently small beta uncertainty (to avoid over-interpreting noisy beta).
    snr_beta_min: float = 2.0,
    beta_stderr_small_max_s_per_m2: float = 2.0e-16,
    config_tag: str = "DQ-01_curved_fit_adequacy_v1",
) -> DR01FitAdequacy1D:
    _ = config_tag

    def _is_dr04(f: DR01FitCurved1D) -> bool:
        tag = str(getattr(f, "tag", "") or "")
        src = str(getattr(f, "source_ref", "") or "")
        hay = (tag + " " + src).upper()
        return ("DR04" in hay) or ("DR-04" in hay) or ("DR_04" in hay)

    requested_policy = str(policy)
    effective_policy = requested_policy

    fail: list[str] = []
    info: list[str] = []
    metrics: dict[str, float] = {
        "policy": 1.0 if str(policy) == "DQ-01_v2" else 0.0,
        "policy_variantA": 1.0 if str(policy) == "DQ-01_variantA" else 0.0,
        "n_points_min": float(n_points_min),
        "rmse_omega_over_k_max_m_per_s": float(rmse_omega_over_k_max_m_per_s),
        "c0_stderr_max_m_per_s": float(c0_stderr_max_m_per_s),
        "rmse_omega_over_k_max_m_per_s_strict_4pt": float(rmse_omega_over_k_max_m_per_s_strict_4pt),
        "c0_stderr_max_m_per_s_strict_4pt": float(c0_stderr_max_m_per_s_strict_4pt),
        "snr_beta_min": float(snr_beta_min),
        "beta_stderr_small_max_s_per_m2": float(beta_stderr_small_max_s_per_m2),
    }

    if requested_policy not in ("DQ-01_v1", "DQ-01_v2", "DQ-01_variantA"):
        raise ValueError("policy must be 'DQ-01_v1', 'DQ-01_v2', or 'DQ-01_variantA'")

    q = fit.fit_quality
    if q is None:
        # VariantA still fails cleanly here; we record the requested policy tag
        # in metrics so the decision is auditable.
        fail.append("missing_fit_quality")
        metrics.update({"n_points": float("nan"), "rmse": float("nan"), "c0_stderr": float("nan"), "beta_stderr": float("nan")})
        return DR01FitAdequacy1D(
            passes=False,
            reason_codes=tuple(fail),
            metrics=metrics,
            input_fingerprint=fit.fingerprint(),
        )

    n_points = int(q.n_points)
    rmse = float(q.rmse_omega_over_k_m_per_s)
    c0_stderr = float(q.c0_stderr_m_per_s)
    beta_stderr = float(q.beta_stderr_s_per_m2)
    beta = float(fit.beta)

    metrics.update(
        {
            "n_points": float(n_points),
            "rmse_omega_over_k_m_per_s": float(rmse),
            "c0_stderr_m_per_s": float(c0_stderr),
            "beta_s_per_m2": float(beta),
            "beta_stderr_s_per_m2": float(beta_stderr),
        }
    )

    # DQ-01_variantA is a scoped overlay: it is only active for DR-04 at N=4.
    # All other windows under this requested policy are evaluated under DQ-01_v1.
    if requested_policy == "DQ-01_variantA":
        effective_policy = "DQ-01_variantA" if (_is_dr04(fit) and n_points == 4) else "DQ-01_v1"

    if n_points < int(n_points_min):
        fail.append("n_points_lt_min")

    if rmse > float(rmse_omega_over_k_max_m_per_s):
        fail.append("rmse_gt_max")

    if c0_stderr > float(c0_stderr_max_m_per_s):
        fail.append("c0_stderr_gt_max")

    beta_snr = float("inf") if beta_stderr == 0.0 else float(abs(beta) / beta_stderr)
    metrics["beta_snr"] = float(beta_snr)

    beta_identifiable = bool((beta_snr >= float(snr_beta_min)) or (beta_stderr <= float(beta_stderr_small_max_s_per_m2)))
    metrics["beta_identifiable"] = 1.0 if beta_identifiable else 0.0

    beta_used_for_inference = True
    if effective_policy == "DQ-01_v2" and n_points == 4:
        beta_used_for_inference = False
        info.append("beta_ignored_low_n")
    if effective_policy == "DQ-01_variantA":
        beta_used_for_inference = False
        info.append("beta_ignored_low_n")
    metrics["beta_used_for_inference"] = 1.0 if beta_used_for_inference else 0.0

    if beta_used_for_inference and (not beta_identifiable):
        fail.append("beta_not_identifiable")

    # DQ-01_v2 tiered exception: if N==4, allow a conditional pass by requiring
    # stricter RMSE and c0 stderr thresholds, and ignoring beta identifiability.
    if effective_policy == "DQ-01_v2" and n_points == 4:
        # Remove the strict N threshold failure if present.
        fail = [r for r in fail if r != "n_points_lt_min"]
        if rmse > float(rmse_omega_over_k_max_m_per_s_strict_4pt):
            fail.append("rmse_gt_max_strict_4pt")
        if c0_stderr > float(c0_stderr_max_m_per_s_strict_4pt):
            fail.append("c0_stderr_gt_max_strict_4pt")

    # DQ-01_variantA: DR-04-only N=4 clause with strict bounds; beta is never a
    # failure mode here (recorded as not used for inference).
    if effective_policy == "DQ-01_variantA":
        fail = [r for r in fail if r not in ("n_points_lt_min", "beta_not_identifiable")]
        if rmse > float(rmse_omega_over_k_max_m_per_s_strict_4pt):
            fail.append("rmse_gt_max_n4_strict")
        if c0_stderr > float(c0_stderr_max_m_per_s_strict_4pt):
            fail.append("c0_stderr_gt_max_n4_strict")

    passes = len(fail) == 0

    reason_codes = tuple(list(fail) + list(info))

    return DR01FitAdequacy1D(
        passes=bool(passes),
        reason_codes=reason_codes,
        metrics=metrics,
        input_fingerprint=fit.fingerprint(),
    )
