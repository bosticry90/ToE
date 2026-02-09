"""FN-01 candidate implementations (internal; import-banned).

Policy:
- This module is not a public surface.
- Downstream code must not import this module directly; it exists only for
  internal experiments and for enforcing a BR-01-style front-door pattern.

If you need a stable reference to a candidate choice, use FN01Artifact1D from
formal.python.toe.constraints.fn01_artifact.
"""

from __future__ import annotations

import numpy as np


def P_cubic(psi: np.ndarray, *, g: float) -> np.ndarray:
    return float(g) * (np.abs(psi) ** 2) * psi
