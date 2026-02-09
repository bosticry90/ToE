from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.rl02_nonrelativistic_nlse_v0 import (
    RL02NLSEReport,
    RL02_TOLERANCE_PROFILE_ENV,
    rl02_compare_surfaces,
    rl02_nonrelativistic_nlse_v0_record,
    rl02_v0_tolerance_profile_from_env,
    rl02_v0_tolerances,
)


def _write_rl02_report(path: Path, report: RL02NLSEReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(
    *,
    k: list[float],
    m: float,
    mu: float,
    epsilon: float,
    config_tag: str,
    regime_tag: str,
) -> RL02NLSEReport:
    omega = [(kk * kk) / (2.0 * float(m)) + float(mu) for kk in k]
    return RL02NLSEReport(
        schema="RL/nr_nlse_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={"m": m, "mu": mu, "epsilon": epsilon},
        k=list(k),
        omega=omega,
    )


def test_rl02_record_is_deterministic_and_schema_stable():
    rec1 = rl02_nonrelativistic_nlse_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rec2 = rl02_nonrelativistic_nlse_v0_record(date="2026-02-09", tolerance_profile="pinned")

    assert rec1.schema == "OV-RL-02_nonrelativistic_nlse_comparator/v0"
    assert rec1.observable_id == "OV-RL-02"
    assert rec1.domain_id == "DRBR-DOMAIN-RL-02"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_rl02_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert rl02_v0_tolerance_profile_from_env({}) == "pinned"
    assert rl02_v0_tolerance_profile_from_env({RL02_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(
        k=[0.0, 0.25, 0.5, 1.0, 2.0],
        m=1.0,
        mu=1.0,
        epsilon=0.01,
        config_tag="rl02-prof-ref",
        regime_tag="rl02-lowk",
    )
    cand = _make_report(
        k=[0.0, 0.25, 0.5, 1.0, 2.0],
        m=1.0,
        mu=1.0,
        epsilon=0.01,
        config_tag="rl02-prof-cand",
        regime_tag="rl02-lowk",
    )
    _write_rl02_report(tmp_path / "rl02_reference_report.json", ref)
    _write_rl02_report(tmp_path / "rl02_candidate_report.json", cand)

    rec = rl02_nonrelativistic_nlse_v0_record(
        date="2026-02-09",
        env={RL02_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_rl02_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        rl02_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "RL/nr_nlse_front_door_report/v1"},
            {"schema": "RL/nr_nlse_front_door_report/v1"},
            tolerances=rl02_v0_tolerances("pinned"),
        )


def test_rl02_negative_control_k_permutation_fails_order_or_alignment():
    k_ref = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = _make_report(k=k_ref, m=1.0, mu=1.0, epsilon=0.01, config_tag="rl02-neg-ref", regime_tag="rl02-lowk")
    cand = _make_report(
        k=[0.0, 0.5, 0.25, 1.0, 2.0],
        m=1.0,
        mu=1.0,
        epsilon=0.01,
        config_tag="rl02-neg-k",
        regime_tag="rl02-lowk",
    )
    row = rl02_compare_surfaces(ref, cand, tolerances=rl02_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert ("FAIL_K_GRID_ORDER" in reasons) or ("FAIL_K_GRID_ALIGNMENT" in reasons)


def test_rl02_negative_control_param_mismatch_fails_domain_consistency():
    k = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = _make_report(k=k, m=1.0, mu=1.0, epsilon=0.01, config_tag="rl02-neg-reg-ref", regime_tag="rl02-lowk")
    cand = _make_report(k=k, m=1.0, mu=1.0, epsilon=0.02, config_tag="rl02-neg-reg-cand", regime_tag="rl02-lowk")
    row = rl02_compare_surfaces(ref, cand, tolerances=rl02_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_DOMAIN_PARAMETER_INCONSISTENT" in reasons


def test_rl02_negative_control_scaling_mismatch_fails_limit_scaling():
    k = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = _make_report(k=k, m=1.0, mu=1.0, epsilon=0.01, config_tag="rl02-neg-scale-ref", regime_tag="rl02-lowk")
    cand = RL02NLSEReport(
        schema="RL/nr_nlse_front_door_report/v1",
        config_tag="rl02-neg-scale-cand",
        regime_tag="rl02-lowk",
        params={"m": 1.0, "mu": 1.0, "epsilon": 0.01},
        k=list(k),
        omega=[(kk * kk) / 2.0 + 1.0 + 0.05 * kk for kk in k],
    )
    row = rl02_compare_surfaces(ref, cand, tolerances=rl02_v0_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_LIMIT_SCALING_MISMATCH" in reasons


def test_rl02_fingerprint_tamper_negative_control_fails_nondeterministic(tmp_path: Path):
    ref = _make_report(k=[0.0, 0.25, 0.5, 1.0, 2.0], m=1.0, mu=1.0, epsilon=0.01, config_tag="rl02-neg-fp-ref", regime_tag="rl02-lowk")
    cand = _make_report(k=[0.0, 0.25, 0.5, 1.0, 2.0], m=1.0, mu=1.0, epsilon=0.01, config_tag="rl02-neg-fp-cand", regime_tag="rl02-lowk")
    _write_rl02_report(tmp_path / "rl02_reference_report.json", ref)
    _write_rl02_report(tmp_path / "rl02_candidate_report.json", cand, tamper_fingerprint=True)

    rec = rl02_nonrelativistic_nlse_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    row = rec.rows[0]
    assert row["passed"] is False
    assert "FAIL_NONDETERMINISTIC_FINGERPRINT" in list(row["reason_codes"])


def test_rl02_blocks_when_artifacts_missing(tmp_path: Path):
    rec = rl02_nonrelativistic_nlse_v0_record(date="2026-02-09", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
