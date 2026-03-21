from __future__ import annotations

from qft_evidence_diversification_cycle_gate_family_helper import (
    QftEvidenceDiversificationCycleSpec,
    register_qft_evidence_diversification_cycle_gate,
)


register_qft_evidence_diversification_cycle_gate(
    globals(),
    QftEvidenceDiversificationCycleSpec(cycle=4),
)



