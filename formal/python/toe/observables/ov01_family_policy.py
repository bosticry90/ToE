"""OV-01h/POL-01: operational policy for OV-based pruning.

This module is intentionally small: it makes the OV-01g decision-grade gate
operational by providing a single front-door selector used by downstream loops.

Policy (current canonical):
- Preferred DR family for OV-based pruning = "curved" iff OV-01g prefers curved
  AND robustness_failed is False.
- Otherwise return "undecided" (downstream must not treat OV pruning as
  decisive for family selection).

Deterministic and contains no filesystem I/O.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import (
    OV01FitFamilyRobustnessReport,
    ov01_fit_family_robustness_gate,
)


OV01PreferredFamily = Literal["curved", "undecided"]


@dataclass(frozen=True)
class OV01FamilySelection:
    preferred_family: OV01PreferredFamily
    gate_report: OV01FitFamilyRobustnessReport


def ov01_preferred_family_for_pruning(
    fn_artifact: FN01Artifact1D,
    dr_fits_linear: list[DR01Fit1D] | tuple[DR01Fit1D, ...],
    dr_fits_curved: list[DR01FitCurved1D] | tuple[DR01FitCurved1D, ...],
    *,
    epsilon: float = 1.0e-12,
    tau_obs: float = 0.10,
    q_threshold: float = 0.90,
    adequacy_policy: str = "DQ-01_v1",
) -> OV01FamilySelection:
    rep = ov01_fit_family_robustness_gate(
        fn_artifact,
        dr_fits_linear,
        dr_fits_curved,
        epsilon=float(epsilon),
        tau_obs=float(tau_obs),
        q_threshold=float(q_threshold),
        adequacy_policy=str(adequacy_policy),
    )

    policy_recorded = bool(str(getattr(rep, "adequacy_policy", "")).strip() != "")
    prefer_curved = bool(policy_recorded and rep.prefer_curved and (not rep.robustness_failed))
    preferred_family: OV01PreferredFamily = "curved" if prefer_curved else "undecided"

    return OV01FamilySelection(preferred_family=preferred_family, gate_report=rep)
