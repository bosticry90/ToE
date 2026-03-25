from __future__ import annotations

import pytest

from sr_m5_cycle_gate_family_helper import SrM5CycleGateSpec, register_sr_m5_cycle_gate


pytestmark = pytest.mark.skip(
    reason="Historical SR M5 cycle gate retained for archive traceability; active gate is registry-driven."
)


register_sr_m5_cycle_gate(
    globals(),
    SrM5CycleGateSpec(cycle=51, status_token="RUN_BOUNDED_v0_NONCLAIM", skip_historical=True),
)
