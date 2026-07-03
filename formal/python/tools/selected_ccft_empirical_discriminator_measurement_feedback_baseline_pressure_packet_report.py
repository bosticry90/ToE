from __future__ import annotations

from formal.python.tools.post_phi_transport_ccft_chain_reports import (
    build_stage_payload,
    stage_main,
)


STAGE_KEY = "measurement_feedback_baseline_pressure_packet"


def build_selected_ccft_empirical_discriminator_measurement_feedback_baseline_pressure_packet() -> (
    dict[str, object]
):
    return build_stage_payload(STAGE_KEY)


if __name__ == "__main__":
    raise SystemExit(stage_main(STAGE_KEY))
