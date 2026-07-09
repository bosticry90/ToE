from __future__ import annotations

from formal.python.tools.post_phi_transport_ccft_chain_reports import (
    build_stage_payload,
    stage_main,
)


STAGE_KEY = (
    "ccft_scqed_literature_applicability_matrix_calculation_result_review"
)


def build_ccft_scqed_literature_applicability_matrix_calculation_result_review() -> dict:
    return build_stage_payload(STAGE_KEY)


if __name__ == "__main__":
    raise SystemExit(stage_main(STAGE_KEY))
