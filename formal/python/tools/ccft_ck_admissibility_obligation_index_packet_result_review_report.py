from __future__ import annotations

from formal.python.tools.post_phi_transport_ccft_chain_reports import (
    STAGES,
    build_stage_payload,
    release_path,
    stage_main,
)


STAGE_KEY = "ck_index_review"
SCHEMA_ID = STAGES[STAGE_KEY].schema_id
PACKET_ID = STAGES[STAGE_KEY].packet_id
OUTCOME_ID = STAGES[STAGE_KEY].outcome_id
STRICT_REVIEW_RESULT = STAGES[STAGE_KEY].strict_outcome_id
DEFAULT_OUT = release_path(STAGES[STAGE_KEY])


def build_ccft_ck_admissibility_obligation_index_packet_result_review():
    return build_stage_payload(STAGE_KEY)


if __name__ == "__main__":
    raise SystemExit(stage_main(STAGE_KEY))
