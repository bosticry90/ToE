"""OV-03x: fit-family robustness gate on a second external dataset.

This module is a thin wrapper around OV-01g's decision-grade gate implementation.

Design constraints
- Deterministic (no RNG).
- No filesystem I/O.

Note
- OV-03x is intended to be *robustness-only* and must not be used for β inference.
"""

from __future__ import annotations

from formal.python.toe.constraints.fn01_artifact import FN01Artifact1D
from formal.python.toe.dr01_fit import DR01Fit1D
from formal.python.toe.dr01_fit_curved import DR01FitCurved1D
from formal.python.toe.observables.ov01_fit_family_robustness import OV01FitFamilyRobustnessReport, ov01_fit_family_robustness_gate


def ov03_fit_family_robustness_gate(
    fn_artifact: FN01Artifact1D,
    dr_fits_linear: list[DR01Fit1D] | tuple[DR01Fit1D, ...],
    dr_fits_curved: list[DR01FitCurved1D] | tuple[DR01FitCurved1D, ...],
    *,
    adequacy_policy: str = "DQ-01_v1",
    q_threshold: float = 0.90,
    config_tag: str = "OV-03x_fit_family_robustness_v1",
) -> OV01FitFamilyRobustnessReport:
    return ov01_fit_family_robustness_gate(
        fn_artifact,
        dr_fits_linear,
        dr_fits_curved,
        q_threshold=float(q_threshold),
        adequacy_policy=str(adequacy_policy),
        config_tag=str(config_tag),
    )
