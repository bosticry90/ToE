from __future__ import annotations

from qft_gr_seam_packet_eligibility_review_checks import run_packet_eligibility_review_checks


def test_qft_gr_seam_packet44_eligibility_review_gate() -> None:
    run_packet_eligibility_review_checks(
        packet_id=44,
        gate_rel_path="formal/python/tests/test_toe_qft_gr_seam_packet44_eligibility_review_gate.py",
    )



