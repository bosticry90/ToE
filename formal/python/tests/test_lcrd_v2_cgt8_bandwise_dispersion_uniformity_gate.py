from __future__ import annotations

import pytest


pytestmark = pytest.mark.skip(
    reason=(
        "Scaffold gate only: pending canonical non-archive LCRD front-door selection. "
        "Non-claim posture and archive import quarantine are preserved."
    )
)


def test_lcrd_v2_cgt8_bandwise_dispersion_uniformity_scaffold_gate() -> None:
    """Scaffold for legacy CG-T8 invariant tracking.

    Legacy source intent:
    - archive/lcrd_legacy_docs/ft_step7_lcrd_v2_test_plan.md (CG-T8)
    - Bandwise small-k dispersion mapping and uniformity checks.

    Promotion rule:
    - Activate only after a canonical non-archive LCRD front-door exists.
    - Re-express using typed inputs and deterministic outputs.
    """
    assert True
