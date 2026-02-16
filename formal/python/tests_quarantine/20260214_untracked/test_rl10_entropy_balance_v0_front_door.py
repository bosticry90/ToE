from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.rl10_entropy_balance_v0 import (
    RL10EntropyReport,
    RL10_TOLERANCE_PROFILE_ENV,
    rl10_compare_surfaces,
    rl10_entropy_balance_v0_record,
    rl10_v0_tolerance_profile_from_env,
    rl10_v0_tolerances,
)
from formal.python.tools.rl10_entropy_balance_front_door import generate_rl10_report


def _write_rl10_report(path: Path, report: RL10EntropyReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> RL10EntropyReport:
    return generate_rl10_report(
        eps_balance=1e-8,
        eps_entropy=1e-3,
        regime_tag=regime_tag,
        config_tag=config_tag,
        domain_tag="rl10-entropy-balance-domain-01",
    )


def test_rl10_record_is_deterministic_and_schema_stable():
    rec1 = rl10_entropy_balance_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl10_entropy_balance_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-10_entropy_balance_comparator/v0"
    assert rec1.observable_id == "OV-RL-10"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-10"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl10_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl10_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl10_v0_tolerance_profile_from_env({RL10_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="rl10-prof-ref", regime_tag="rl10-entropy-balance")
    cand = _make_report(config_tag="rl10-prof-cand", regime_tag="rl10-entropy-balance")
    _write_rl10_report(tmp_path / "rl10_reference_report.json", ref)
    _write_rl10_report(tmp_path / "rl10_candidate_report.json", cand)

    rec = rl10_entropy_balance_v0_record(
        date="2026-02-09",
        env={RL10_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl10_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl10_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/entropy_balance_front_door_report/v1"},
            {"schema": "RL/entropy_balance_front_door_report/v1"},
            tolerances=rl10_v0_tolerances("pinned"),
        )


def test_rl10_entropy_controls_pass():
    report = _make_report(config_tag="rl10-ref", regime_tag="rl10-entropy-balance")
    rows = rl10_compare_surfaces(report, report, tolerances=rl10_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True


def test_rl10_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="rl10-neg-fp-ref", regime_tag="rl10-entropy-balance")
    cand = _make_report(config_tag="rl10-neg-fp-cand", regime_tag="rl10-entropy-balance")
    _write_rl10_report(tmp_path / "rl10_reference_report.json", ref)
    _write_rl10_report(tmp_path / "rl10_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl10_entropy_balance_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_rl10_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl10_entropy_balance_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
