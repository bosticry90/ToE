from __future__ import annotations

from pathlib import Path

from formal.python.toe.observables.ovdq01_dq01_diagnostics_record import (
    _extract_json_block,
    _extract_report_fingerprint,
    ovdq01_dq01_diagnostics_record,
)


def test_ov_dq01_lock_payload_fingerprint_matches_file() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    lock_path = (
        repo_root
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-DQ-01_dq01_diagnostics_record.md"
    )
    md = lock_path.read_text(encoding="utf-8")

    payload = _extract_json_block(md)
    fp = _extract_report_fingerprint(md)

    rec = ovdq01_dq01_diagnostics_record(adequacy_policy=str(payload["adequacy_policy"]))
    assert payload == rec.to_jsonable()
    assert fp == rec.fingerprint()
