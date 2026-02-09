"""OV-02x: digitization-invariance robustness gate (metamorphic check).

Purpose
-------
Provide an empirical-anchor candidate *outside the DR-family* by anchoring a
measurement/instrument invariance claim:

    Small, pre-registered perturbations to the digitized external dataset
    (within a declared tolerance) do not flip the OV-01g robustness preference.

Interpretation guardrail
------------------------
- This is a stability/robustness anchor. It is not a parameter-inference claim.
- It must not be used to imply beta is nonzero or physically inferred.

Design constraints
------------------
- Deterministic (no RNG).
- No filesystem I/O.
- Uses the same decision-grade OV-01g gate as the downstream selector.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Iterable, Literal, Sequence

from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D, dr01_fit_curved_from_sample_kw
from formal.python.toe.observables.ov01_fit_family_robustness import (
    OV01FitFamilyRobustnessReport,
    ov01_fit_family_robustness_gate,
)


def _sha256_json(payload: object) -> str:
    b = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    return hashlib.sha256(b).hexdigest()


def _fit_through_origin(sample_kw: Sequence[tuple[float, float]]) -> float:
    # Through-origin least squares for omega ~= c_s * k with k>0.
    sxx = sum(float(k) * float(k) for (k, _) in sample_kw)
    if sxx == 0.0:
        raise ValueError("Degenerate sample: sum(k^2)==0")
    sxy = sum(float(k) * float(w) for (k, w) in sample_kw)
    return float(sxy / sxx)


def _make_linear_fit_from_sample_kw(
    sample_kw: Sequence[tuple[float, float]],
    *,
    tag: str,
    source_kind: Literal["csv", "manual", "synthetic", "unknown"] = "csv",
    source_ref: str | None = None,
    fit_method_tag: str = "digitization-perturbed through-origin omega=c_s*k",
) -> DR01Fit1D:
    c_s = _fit_through_origin(sample_kw)
    return DR01Fit1D(
        u=0.0,
        c_s=float(c_s),
        tag=str(tag),
        source_kind=source_kind,
        source_ref=source_ref,
        sample_kw=tuple((float(k), float(w)) for (k, w) in sample_kw),
        fit_method_tag=str(fit_method_tag),
    )


def _canonicalize_sample_kw(sample_kw: Iterable[tuple[float, float]]) -> tuple[tuple[float, float], ...]:
    items = [(float(k), float(w)) for (k, w) in sample_kw]
    items.sort(key=lambda t: (t[0], t[1]))
    return tuple(items)


def _union_k_index(windows: Sequence[Sequence[tuple[float, float]]]) -> dict[float, int]:
    ks: set[float] = set()
    for w in windows:
        for k, _ in w:
            ks.add(float(k))
    ks_sorted = sorted(ks)
    return {k: i for i, k in enumerate(ks_sorted)}


def _perturb_multiplier(
    *,
    pattern: str,
    k: float,
    k_index: dict[float, int],
    rel_eps: float,
) -> float:
    if rel_eps < 0.0:
        raise ValueError("rel_eps must be non-negative")
    if rel_eps == 0.0:
        return 1.0

    idx = k_index[float(k)]
    n = max(1, len(k_index))

    if pattern == "baseline":
        return 1.0
    if pattern == "all_plus":
        return 1.0 + float(rel_eps)
    if pattern == "all_minus":
        return 1.0 - float(rel_eps)
    if pattern == "alt_pm":
        s = 1.0 if (idx % 2 == 0) else -1.0
        return 1.0 + s * float(rel_eps)
    if pattern == "ramp":
        # Deterministic ramp in [-rel_eps, +rel_eps] over sorted k indices.
        if n == 1:
            return 1.0
        t = (2.0 * idx / (n - 1)) - 1.0
        return 1.0 + float(rel_eps) * float(t)

    raise ValueError(f"Unknown perturbation pattern: {pattern!r}")


def perturb_digitization_omega(
    sample_kw: Sequence[tuple[float, float]],
    *,
    rel_eps: float,
    pattern: str,
    k_index: dict[float, int],
) -> tuple[tuple[float, float], ...]:
    """Apply a deterministic, bounded multiplicative perturbation to omega values.

    This is intended as a proxy for modest digitization choices within tolerance.
    """

    base = _canonicalize_sample_kw(sample_kw)
    out: list[tuple[float, float]] = []
    for k, w in base:
        m = _perturb_multiplier(pattern=pattern, k=k, k_index=k_index, rel_eps=float(rel_eps))
        out.append((float(k), float(w) * float(m)))
    return tuple(out)


@dataclass(frozen=True)
class OV02DigitizationInvarianceScenario:
    pattern: str
    rel_eps: float
    ov01g_prefer_curved: bool
    ov01g_robustness_failed: bool
    ov01g_q_ratio: float
    ov01g_curved_adequacy_passes: bool
    ov01g_fingerprint: str


@dataclass(frozen=True)
class OV02DigitizationInvarianceReport:
    config_tag: str
    adequacy_policy: str

    rel_eps: float
    patterns: tuple[str, ...]

    baseline_prefer_curved: bool
    all_scenarios_match_baseline: bool
    robustness_failed: bool

    scenarios: tuple[OV02DigitizationInvarianceScenario, ...]

    def fingerprint(self) -> str:
        payload = {
            "config_tag": self.config_tag,
            "adequacy_policy": self.adequacy_policy,
            "rel_eps": float(self.rel_eps),
            "patterns": list(self.patterns),
            "baseline_prefer_curved": bool(self.baseline_prefer_curved),
            "all_scenarios_match_baseline": bool(self.all_scenarios_match_baseline),
            "robustness_failed": bool(self.robustness_failed),
            "scenarios": [
                {
                    "pattern": s.pattern,
                    "rel_eps": float(s.rel_eps),
                    "ov01g_prefer_curved": bool(s.ov01g_prefer_curved),
                    "ov01g_robustness_failed": bool(s.ov01g_robustness_failed),
                    "ov01g_q_ratio": float(s.ov01g_q_ratio),
                    "ov01g_curved_adequacy_passes": bool(s.ov01g_curved_adequacy_passes),
                    "ov01g_fingerprint": str(s.ov01g_fingerprint),
                }
                for s in self.scenarios
            ],
        }
        return _sha256_json(payload)


def ov02_digitization_invariance_gate(
    fn_artifact: FN01Artifact1D,
    *,
    windows_sample_kw: Sequence[Sequence[tuple[float, float]]],
    rel_eps: float = 0.01,
    patterns: Sequence[str] = ("baseline", "alt_pm", "ramp"),
    q_threshold: float = 0.90,
    adequacy_policy: str = "DQ-01_v1",
    config_tag: str = "OV-02x_digitization_invariance_v1",
) -> OV02DigitizationInvarianceReport:
    """Compute whether OV-01g preference is invariant under bounded perturbations."""

    if rel_eps < 0.0:
        raise ValueError("rel_eps must be non-negative")
    if not patterns:
        raise ValueError("patterns must be non-empty")
    if q_threshold <= 0.0:
        raise ValueError("q_threshold must be positive")

    # Canonicalize inputs
    base_windows = [
        _canonicalize_sample_kw(w) for w in list(windows_sample_kw)
    ]

    k_index = _union_k_index(base_windows)

    scenarios: list[OV02DigitizationInvarianceScenario] = []

    baseline_prefer_curved: bool | None = None

    for pat in list(patterns):
        pert_windows = [
            perturb_digitization_omega(w, rel_eps=float(rel_eps), pattern=str(pat), k_index=k_index)
            for w in base_windows
        ]

        # Fit linear + curved artifacts per window under this perturbation.
        linear_fits: list[DR01Fit1D] = []
        curved_fits: list[DR01FitCurved1D] = []

        for i, sample_kw in enumerate(pert_windows):
            linear_fits.append(
                _make_linear_fit_from_sample_kw(
                    sample_kw,
                    tag=f"ov02_lin_w{i}_{pat}",
                    source_ref="digitization-invariance perturbation (omega scaled)",
                )
            )
            curved_fits.append(
                dr01_fit_curved_from_sample_kw(
                    sample_kw,
                    u_fixed=0.0,
                    tag=f"ov02_curv_w{i}_{pat}",
                    source_kind="csv",
                    source_ref="digitization-invariance perturbation (omega scaled)",
                )
            )

        rep: OV01FitFamilyRobustnessReport = ov01_fit_family_robustness_gate(
            fn_artifact,
            linear_fits,
            curved_fits,
            q_threshold=float(q_threshold),
            adequacy_policy=str(adequacy_policy),
        )

        sc = OV02DigitizationInvarianceScenario(
            pattern=str(pat),
            rel_eps=float(rel_eps),
            ov01g_prefer_curved=bool(rep.prefer_curved),
            ov01g_robustness_failed=bool(rep.robustness_failed),
            ov01g_q_ratio=float(rep.q_ratio),
            ov01g_curved_adequacy_passes=bool(rep.curved_adequacy_passes),
            ov01g_fingerprint=str(rep.fingerprint()),
        )
        scenarios.append(sc)

        if pat == "baseline":
            baseline_prefer_curved = bool(rep.prefer_curved)

    if baseline_prefer_curved is None:
        raise ValueError("patterns must include 'baseline'")

    all_match = all(s.ov01g_prefer_curved == baseline_prefer_curved for s in scenarios)

    # Treat any mismatch as a robustness failure for invariance.
    robustness_failed = bool(not all_match)

    return OV02DigitizationInvarianceReport(
        config_tag=str(config_tag),
        adequacy_policy=str(adequacy_policy),
        rel_eps=float(rel_eps),
        patterns=tuple(str(p) for p in patterns),
        baseline_prefer_curved=bool(baseline_prefer_curved),
        all_scenarios_match_baseline=bool(all_match),
        robustness_failed=bool(robustness_failed),
        scenarios=tuple(scenarios),
    )
