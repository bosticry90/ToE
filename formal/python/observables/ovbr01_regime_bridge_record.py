"""Compatibility wrapper for OV-BR-01.

The repo's primary observable modules live under `formal/python/toe/observables/`.
This wrapper exists to satisfy older path references without duplicating logic.
"""

from __future__ import annotations

from formal.python.toe.observables.ovbr01_regime_bridge_record import (  # noqa: F401
    OVBR01RegimeBridgeRecord,
    ovbr01_regime_bridge_record,
    render_ovbr01_lock_markdown,
    write_ovbr01_lock,
)
