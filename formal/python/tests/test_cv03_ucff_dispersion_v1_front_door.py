from __future__ import annotations

import json
from pathlib import Path
import re

import pytest

from formal.python.toe.comparators.cv03_ucff_dispersion_v1 import (
    CV03_TOLERANCE_PROFILE_ENV,
    cv03_compare_dispersion_surfaces,
    cv03_ucff_dispersion_v1_record,
    cv03_v1_tolerance_profile_from_env,
    cv03_v1_tolerances,
    render_cv03_lock_markdown,
)
from formal.python.toe.ucff.core_front_door import UcffCoreInput, UcffCoreParams, UcffCoreReport, ucff_core_report


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    assert m is not None
    return json.loads(m.group(1))


def _write_ucff_report(path: Path, report: UcffCoreReport, *, tamper_fingerprint: bool = False) -> None:
    payload = report.to_jsonable()
    if tamper_fingerprint:
        payload["fingerprint"] = "tampered"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def test_cv03_record_is_deterministic_and_schema_stable():
    rec1 = cv03_ucff_dispersion_v1_record(date="2026-02-08", tolerance_profile="pinned")
    rec2 = cv03_ucff_dispersion_v1_record(date="2026-02-08", tolerance_profile="pinned")

    assert rec1.schema == "OV-CV-03_ucff_dispersion_comparator/v1"
    assert rec1.observable_id == "OV-CV-03"
    assert rec1.domain_id == "DRBR-DOMAIN-UCFF-01"
    assert rec1.comparator_role == "discriminative_candidate"
    assert rec1.tolerance_profile == "pinned"

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()


def test_cv03_default_profile_is_pinned_and_portable_can_be_selected():
    assert cv03_v1_tolerance_profile_from_env({}) == "pinned"
    assert cv03_v1_tolerance_profile_from_env({CV03_TOLERANCE_PROFILE_ENV: "portable"}) == "portable"

    rec = cv03_ucff_dispersion_v1_record(date="2026-02-08", env={CV03_TOLERANCE_PROFILE_ENV: "portable"})
    assert rec.tolerance_profile == "portable"
    assert rec.status["blocked"] is False


def test_cv03_front_door_requires_typed_reports():
    with pytest.raises(TypeError):
        cv03_compare_dispersion_surfaces(  # type: ignore[arg-type]
            {"schema": "UCFF/core_front_door_report/v1"},
            {"schema": "UCFF/core_front_door_report/v1"},
            tolerances=cv03_v1_tolerances("pinned"),
        )


def test_cv03_negative_control_k_permutation_fails_order_or_alignment():
    k_ref = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = ucff_core_report(
        UcffCoreInput(k=k_ref, params=UcffCoreParams(rho0=1.0, g=0.0, lam=0.0, beta=0.0), config_tag="cv03-neg-ref")
    )
    cand = ucff_core_report(
        UcffCoreInput(k=[0.0, 0.5, 0.25, 1.0, 2.0], params=UcffCoreParams(rho0=1.0, g=0.0, lam=0.0, beta=0.0), config_tag="cv03-neg-k-permute")
    )
    row = cv03_compare_dispersion_surfaces(ref, cand, tolerances=cv03_v1_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert ("FAIL_K_GRID_ORDER" in reasons) or ("FAIL_K_GRID_ALIGNMENT" in reasons)


def test_cv03_negative_control_sign_flip_fails_sign_policy():
    k = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = ucff_core_report(
        UcffCoreInput(k=k, params=UcffCoreParams(rho0=1.0, g=0.0, lam=0.0, beta=0.0), config_tag="cv03-neg-sign-ref")
    )
    cand = ucff_core_report(
        UcffCoreInput(k=k, params=UcffCoreParams(rho0=1.0, g=-1.0, lam=0.0, beta=0.0), config_tag="cv03-neg-sign-cand")
    )
    row = cv03_compare_dispersion_surfaces(ref, cand, tolerances=cv03_v1_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_DISPERSION_SIGN" in reasons


def test_cv03_negative_control_shape_perturbation_fails_shape_mismatch():
    k = [0.0, 0.25, 0.5, 1.0, 2.0]
    ref = ucff_core_report(
        UcffCoreInput(k=k, params=UcffCoreParams(rho0=1.0, g=0.0, lam=0.0, beta=0.0), config_tag="cv03-neg-shape-ref")
    )
    cand = ucff_core_report(
        UcffCoreInput(k=k, params=UcffCoreParams(rho0=1.0, g=0.0, lam=0.25, beta=0.0), config_tag="cv03-neg-shape-cand")
    )
    row = cv03_compare_dispersion_surfaces(ref, cand, tolerances=cv03_v1_tolerances("pinned"))
    reasons = list(row["reason_codes"])
    assert row["passed"] is False
    assert "FAIL_DISPERSION_SHAPE_MISMATCH" in reasons


def test_cv03_fingerprint_tamper_negative_control_fails_nondeterministic(tmp_path: Path):
    ref = ucff_core_report(
        UcffCoreInput(
            k=[0.0, 0.25, 0.5, 1.0, 2.0],
            params=UcffCoreParams(rho0=1.0, g=0.0, lam=0.0, beta=0.0),
            config_tag="cv03-neg-fp-ref",
        )
    )
    cand = ucff_core_report(
        UcffCoreInput(
            k=[0.0, 0.25, 0.5, 1.0, 2.0],
            params=UcffCoreParams(rho0=1.0, g=0.0, lam=0.0, beta=0.0),
            config_tag="cv03-neg-fp-cand",
        )
    )
    _write_ucff_report(tmp_path / "cv03_reference_ucff_core_report.json", ref)
    _write_ucff_report(tmp_path / "cv03_candidate_ucff_core_report.json", cand, tamper_fingerprint=True)

    rec = cv03_ucff_dispersion_v1_record(date="2026-02-08", tolerance_profile="pinned", artifact_dir=tmp_path)
    assert rec.status["blocked"] is False
    row = rec.rows[0]
    assert row["passed"] is False
    assert "FAIL_DISPERSION_NONDETERMINISTIC" in list(row["reason_codes"])


def test_cv03_blocks_when_artifacts_missing(tmp_path: Path):
    rec = cv03_ucff_dispersion_v1_record(date="2026-02-08", tolerance_profile="pinned", artifact_dir=tmp_path / "missing")
    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_domain_artifacts"]
    assert rec.rows == []
    assert rec.summary["counts"] == {"pass": 0, "fail": 0}
    assert rec.summary["artifacts"] == {"pass": [], "fail": []}


def test_cv03_lock_render_contains_record_and_fingerprint():
    rec = cv03_ucff_dispersion_v1_record(date="2026-02-08", tolerance_profile="pinned")
    md = render_cv03_lock_markdown(rec)
    payload = _extract_json_block(md)
    assert payload == rec.to_jsonable()
    assert f"Record fingerprint: `{rec.fingerprint()}`" in md
