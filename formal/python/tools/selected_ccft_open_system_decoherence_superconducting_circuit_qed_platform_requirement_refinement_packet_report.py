"""Emit the selected CCFT superconducting circuit-QED platform requirement packet."""

from __future__ import annotations

from formal.python.tools.post_phi_transport_ccft_chain_reports import (
    build_stage_payload,
    stage_main,
)


STAGE_KEY = (
    "baseline_component_equation_source_applicability_gap_resolution_"
    "open_system_decoherence_superconducting_circuit_qed_platform_"
    "requirement_refinement_packet"
)


def build_selected_ccft_open_system_decoherence_superconducting_circuit_qed_platform_requirement_refinement_packet():
    return build_stage_payload(STAGE_KEY)


if __name__ == "__main__":
    stage_main(STAGE_KEY)
