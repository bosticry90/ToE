from __future__ import annotations

import pytest

from qft_gr_seam_packet_eligibility_review_checks import run_packet_eligibility_review_checks


@pytest.mark.parametrize("packet_id", [42, 43, 44])
def test_qft_gr_seam_packet_eligibility_review_gate_family(packet_id: int) -> None:
    gate_rel_path = (
        f"formal/python/tests/test_toe_qft_gr_seam_packet{packet_id}_eligibility_review_gate.py"
    )
    run_packet_eligibility_review_checks(packet_id=packet_id, gate_rel_path=gate_rel_path)
