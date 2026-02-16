from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.rl11_causality_signal_cone_v0 import (
    RL11CausalityReport,
    RL11_TOLERANCE_PROFILE_ENV,
    rl11_causality_signal_cone_v0_record,
    rl11_compare_surfaces,
    rl11_v0_tolerance_profile_from_env,
    rl11_v0_tolerances,
)
from formal.python.tools.rl11_causality_signal_cone_front_door import generate_rl11_report


def _write_rl11_report(path: Path, report: RL11CausalityReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str) -> RL11CausalityReport:
    return generate_rl11_report(
        length=6.283185307179586,
        nx=256,
        dt_pos=0.01,
        dt_neg=0.05,
        steps=10,
        c0=1.0,
        cfl_max=1.0,
        eps_causal=1e-10,
        eps_acausal=1e-3,
        regime_tag=regime_tag,
        config_tag=config_tag,
        domain_tag="rl11-causality-signal-cone-domain-01",
    )


def test_rl11_record_is_deterministic_and_schema_stable():
    rec1 = rl11_causality_signal_cone_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl11_causality_signal_cone_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-11_causality_signal_cone_comparator/v0"
    assert rec1.observable_id == "OV-RL-11"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-11"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl11_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl11_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl11_v0_tolerance_profile_from_env({RL11_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="rl11-prof-ref", regime_tag="rl11-causality-signal-cone")
    cand = _make_report(config_tag="rl11-prof-cand", regime_tag="rl11-causality-signal-cone")
    _write_rl11_report(tmp_path / "rl11_reference_report.json", ref)
    _write_rl11_report(tmp_path / "rl11_candidate_report.json", cand)

    rec = rl11_causality_signal_cone_v0_record(
        date="2026-02-09",
        env={RL11_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl11_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl11_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/causality_signal_cone_front_door_report/v1"},
            {"schema": "RL/causality_signal_cone_front_door_report/v1"},
            tolerances=rl11_v0_tolerances("pinned"),
        )


def test_rl11_causality_controls_pass():
    report = _make_report(config_tag="rl11-ref", regime_tag="rl11-causality-signal-cone")
    rows = rl11_compare_surfaces(report, report, tolerances=rl11_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True


def test_rl11_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="rl11-neg-fp-ref", regime_tag="rl11-causality-signal-cone")
    cand = _make_report(config_tag="rl11-neg-fp-cand", regime_tag="rl11-causality-signal-cone")
    _write_rl11_report(tmp_path / "rl11_reference_report.json", ref)
    _write_rl11_report(tmp_path / "rl11_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl11_causality_signal_cone_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_rl11_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl11_causality_signal_cone_v0_record(
        date="2026-02-09",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
