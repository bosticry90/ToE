from __future__ import annotations

import json

from formal.python.toe.observables.ovdq01_policy_sensitivity_record import ovdq01_policy_sensitivity_record


def test_dq01_v2_q_threshold_105_only_unblocks_ov03x_in_evaluated_set() -> None:
    rec = ovdq01_policy_sensitivity_record().to_jsonable()

    def _row(section: dict, t: float) -> dict:
        for r in list(section["grid"]):
            if abs(float(r["q_threshold"]) - float(t)) <= 1e-12:
                return r
        raise AssertionError(f"Missing row at {t}")

    t1 = 0.90
    t2 = 1.05

    # OV-01g unchanged (already prefers curved well below 0.90).
    r1 = _row(rec["ov01g"], t1)
    r2 = _row(rec["ov01g"], t2)
    assert bool(r1["would_prefer_curved"]) is True
    assert bool(r2["would_prefer_curved"]) is True

    # OV-02x invariance unchanged and baseline preference unchanged.
    r1 = _row(rec["ov02x"], t1)
    r2 = _row(rec["ov02x"], t2)
    assert bool(r1["baseline_prefer_curved"]) is True
    assert bool(r2["baseline_prefer_curved"]) is True
    assert bool(r1["robustness_failed"]) is False
    assert bool(r2["robustness_failed"]) is False

    # OV-04x unchanged (already decisive_curved).
    r1 = _row(rec["ov04x"], t1)
    r2 = _row(rec["ov04x"], t2)
    assert bool(r1["would_prefer_curved"]) is True
    assert bool(r2["would_prefer_curved"]) is True

    # OV-03x flips from blocked to unblocked at 1.05.
    r1 = _row(rec["ov03x"], t1)
    r2 = _row(rec["ov03x"], t2)
    assert bool(r1["would_prefer_curved"]) is False
    assert bool(r2["would_prefer_curved"]) is True
    assert "q_ratio_above_threshold" in list(r1["blocking_reasons"])
    assert list(r2["blocking_reasons"]) == []
