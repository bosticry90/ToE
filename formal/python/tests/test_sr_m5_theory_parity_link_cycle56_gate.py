from __future__ import annotations

from sr_m5_cycle_gate_family_helper import SrM5CycleGateSpec, register_sr_m5_cycle_gate


register_sr_m5_cycle_gate(
    globals(),
    SrM5CycleGateSpec(cycle=56, status_token="COMPLETE_BOUNDED_v0", skip_historical=False),
)
