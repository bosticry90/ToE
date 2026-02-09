"""Compatibility wrapper for OV-04x.

The repo's primary observable modules live under `formal/python/toe/observables/`.
This wrapper exists to satisfy older path references without duplicating logic.
"""

from __future__ import annotations

from formal.python.toe.observables.ov04_fit_family_robustness_lowk_ds02 import (  # noqa: F401
    ov04_fit_family_robustness_gate,
)
