from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.comparators.cx01_update_contractivity_v0 import (
    CX01ContractivityCase,
    CX01ContractivityReport,
    CX01_TOLERANCE_PROFILE_ENV,
    cx01_compare_surfaces,
    cx01_update_contractivity_v0_record,
    cx01_v0_tolerance_profile_from_env,
    cx01_v0_tolerances,
)
from formal.python.tools.cx01_update_contractivity_front_door import build_cx01_reports


def _write_cx01_report(path: Path, report: CX01ContractivityReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, config_tag: str, regime_tag: str, tolerance_profile: str = "pinned") -> CX01ContractivityReport:
    report, _ = build_cx01_reports(tolerance_profile=tolerance_profile)
    payload = report.to_jsonable()
    payload["config_tag"] = config_tag
    payload["regime_tag"] = regime_tag
    return CX01ContractivityReport(
        schema=payload["schema"],
        config_tag=payload["config_tag"],
        regime_tag=payload["regime_tag"],
        domain_tag=payload["domain_tag"],
        params={k: float(v) for k, v in payload["params"].items()},
        norm_name=str(payload["norm_name"]),
        cases=[
            CX01ContractivityCase(
                case_id=str(case["case_id"]),
                kind=str(case["kind"]),
                update_mode=str(case["update_mode"]),
                contraction_factor_per_step=float(case["contraction_factor_per_step"]),
                steps=int(case["steps"]),
                distance_in=float(case["distance_in"]),
                distance_out=float(case["distance_out"]),
                empirical_lipschitz=float(case["empirical_lipschitz"]),
            )
            for case in payload["cases"]
        ],
    )


def _candidate_with_negative_break_removed(report: CX01ContractivityReport) -> CX01ContractivityReport:
    cases: list[CX01ContractivityCase] = []
    for case in report.cases:
        if case.kind == "negative_control":
            cases.append(
                CX01ContractivityCase(
                    case_id=case.case_id,
                    kind=case.kind,
                    update_mode=case.update_mode,
                    contraction_factor_per_step=case.contraction_factor_per_step,
                    steps=case.steps,
                    distance_in=case.distance_in,
                    distance_out=case.distance_in,
                    empirical_lipschitz=1.0,
                )
            )
        else:
            cases.append(case)
    return CX01ContractivityReport(
        schema=report.schema,
        config_tag=report.config_tag,
        regime_tag=report.regime_tag,
        domain_tag=report.domain_tag,
        params=dict(report.params),
        norm_name=report.norm_name,
        cases=cases,
    )


def test_cx01_record_is_deterministic_and_schema_stable():
    rec1 = cx01_update_contractivity_v0_record(date="2026-02-11", tolerance_profile="pinned")
    rec2 = cx01_update_contractivity_v0_record(date="2026-02-11", tolerance_profile="pinned")

    assert rec1.schema == "CX-01_update_contractivity_comparator/v0"
    assert rec1.observable_id == "CX-01"
    assert rec1.domain_id == "CX-DOMAIN-01"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_cx01_default_profile_is_pinned_and_portable_can_be_selected(tmp_path: Path):
    assert cx01_v0_tolerance_profile_from_env({}) == "pinned"
    assert cx01_v0_tolerance_profile_from_env({CX01_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    ref = _make_report(config_tag="cx01-prof-ref", regime_tag="cx01-contractivity", tolerance_profile="portable")
    cand = _make_report(config_tag="cx01-prof-cand", regime_tag="cx01-contractivity", tolerance_profile="portable")
    _write_cx01_report(tmp_path / "cx01_reference_report.json", ref)
    _write_cx01_report(tmp_path / "cx01_candidate_report.json", cand)

    rec = cx01_update_contractivity_v0_record(
        date="2026-02-11",
        env={CX01_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_cx01_profile_mismatch_between_artifact_and_comparator_is_detected(tmp_path: Path):
    # Pinned artifacts compared under portable profile should fail via domain inconsistency.
    ref = _make_report(config_tag="cx01-prof-mismatch-ref", regime_tag="cx01-contractivity", tolerance_profile="pinned")
    cand = _make_report(config_tag="cx01-prof-mismatch-cand", regime_tag="cx01-contractivity", tolerance_profile="pinned")
    _write_cx01_report(tmp_path / "cx01_reference_report.json", ref)
    _write_cx01_report(tmp_path / "cx01_candidate_report.json", cand)

    rec = cx01_update_contractivity_v0_record(
        date="2026-02-11",
        env={CX01_TOLERANCE_PROFILE_ENV: "portable"},
        artifact_dir=tmp_path,
    )
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False
    assert rec.summary["counts"]["fail"] == 2
    assert all("FAIL_DOMAIN_PARAMETER_INCONSISTENT" in row["reason_codes"] for row in rec.rows)


def test_cx01_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        cx01_compare_surfaces(  # type: ignore[arg-type]
            {"schema": "CX-01/update_contractivity_front_door_report/v1"},
            {"schema": "CX-01/update_contractivity_front_door_report/v1"},
            tolerances=cx01_v0_tolerances("pinned"),
        )


def test_cx01_controls_pass_with_expectation_aware_semantics():
    report = _make_report(config_tag="cx01-ref", regime_tag="cx01-contractivity")
    rows = cx01_compare_surfaces(report, report, tolerances=cx01_v0_tolerances("pinned"))
    pos_rows = [row for row in rows if row["source"]["case_kind"] == "positive_control"]
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(pos_rows) == 1
    assert len(neg_rows) == 1
    assert pos_rows[0]["passed"] is True
    assert neg_rows[0]["passed"] is True
    assert "cx01_contractivity_break_detected" in neg_rows[0]["reason_codes"]


def test_cx01_negative_control_break_not_detected_fails():
    report = _make_report(config_tag="cx01-ref", regime_tag="cx01-contractivity")
    candidate = _candidate_with_negative_break_removed(report)
    rows = cx01_compare_surfaces(report, candidate, tolerances=cx01_v0_tolerances("pinned"))
    neg_rows = [row for row in rows if row["source"]["case_kind"] == "negative_control"]
    assert len(neg_rows) == 1
    assert neg_rows[0]["passed"] is False
    assert "FAIL_BREAK_NOT_DETECTED" in neg_rows[0]["reason_codes"]


def test_cx01_config_tag_difference_is_non_binding_metadata():
    ref = _make_report(config_tag="cx01-config-ref", regime_tag="cx01-contractivity")
    cand = _make_report(config_tag="cx01-config-cand", regime_tag="cx01-contractivity")

    rows = cx01_compare_surfaces(ref, cand, tolerances=cx01_v0_tolerances("pinned"))
    assert len(rows) == 2
    assert all(row["passed"] is True for row in rows)
    assert all(row["source"]["reference_config_tag"] != row["source"]["candidate_config_tag"] for row in rows)


def test_cx01_fingerprint_tamper_marks_nondeterministic(tmp_path: Path):
    ref = _make_report(config_tag="cx01-neg-fp-ref", regime_tag="cx01-contractivity")
    cand = _make_report(config_tag="cx01-neg-fp-cand", regime_tag="cx01-contractivity")
    _write_cx01_report(tmp_path / "cx01_reference_report.json", ref)
    _write_cx01_report(tmp_path / "cx01_candidate_report.json", cand, tamper_fingerprint=True)

    rec = cx01_update_contractivity_v0_record(date="2026-02-11", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    fail_rows = [row for row in rec.rows if "FAIL_NONDETERMINISTIC_FINGERPRINT" in row["reason_codes"]]
    assert len(fail_rows) >= 1


def test_cx01_blocks_when_artifacts_missing(tmp_path: Path):
    rec = cx01_update_contractivity_v0_record(
        date="2026-02-11",
        tolerance_profile="pinned",
        artifact_dir=tmp_path / "missing",
    )
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}
