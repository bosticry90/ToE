from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.comparators.rl01_relativistic_dispersion_v0 import (
    RL01DispersionReport,
    rl01_relativistic_dispersion_v0_record,
)


TOP_LEVEL_KEYS = {
    "schema",
    "date",
    "observable_id",
    "domain_id",
    "comparator_role",
    "tolerance_profile",
    "status",
    "inputs",
    "rows",
    "summary",
    "scope_limits",
    "fingerprint",
}

ROW_KEYS = {
    "artifact_id",
    "source",
    "input_fingerprint",
    "input_data_fingerprint",
    "metric_vector",
    "passed",
    "reason_codes",
    "diagnostics",
}

ALLOWED_REASON_CODES = {
    "rl01_relativistic_dispersion_constraints_satisfied",
    "FAIL_REL_LIMIT_SHAPE_MISMATCH",
    "FAIL_REL_LIMIT_NONDETERMINISTIC",
    "FAIL_K_GRID_ORDER",
    "FAIL_K_GRID_ALIGNMENT",
    "FAIL_REGIME_MISMATCH",
}


def _write_rl01_report(path: Path, report: RL01DispersionReport) -> None:
    payload = report.to_jsonable()
    path.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n", encoding="utf-8")


def _make_report(*, k: list[float], c: float, m: float, config_tag: str, regime_tag: str) -> RL01DispersionReport:
    omega2 = [(c * c) * (kk * kk) + (m * m) for kk in k]
    return RL01DispersionReport(
        schema="RL/dispersion_front_door_report/v1",
        config_tag=config_tag,
        regime_tag=regime_tag,
        params={"c": c, "m": m},
        k=list(k),
        omega2=omega2,
    )


def _record_with_artifacts(tmp_path: Path):
    ref = _make_report(k=[0.0, 0.25, 0.5, 1.0, 2.0], c=1.0, m=1.0, config_tag="rl01-freeze-ref", regime_tag="rl01-lowk")
    cand = _make_report(k=[0.0, 0.25, 0.5, 1.0, 2.0], c=1.0, m=1.0, config_tag="rl01-freeze-cand", regime_tag="rl01-lowk")
    _write_rl01_report(tmp_path / "rl01_reference_report.json", ref)
    _write_rl01_report(tmp_path / "rl01_candidate_report.json", cand)
    return rl01_relativistic_dispersion_v0_record(date="2026-02-08", tolerance_profile="pinned", artifact_dir=tmp_path)


def test_rl01_surface_contract_top_level_keys_frozen(tmp_path: Path):
    rec = _record_with_artifacts(tmp_path)
    payload = rec.to_jsonable()

    assert payload["schema"] == "OV-RL-01_relativistic_dispersion_comparator/v0"
    assert payload["observable_id"] == "OV-RL-01"
    assert payload["domain_id"] == "DRBR-DOMAIN-RL-01"
    assert payload["comparator_role"] == "discriminative_candidate"
    assert payload["tolerance_profile"] == "pinned"
    assert set(payload.keys()) == TOP_LEVEL_KEYS


def test_rl01_surface_contract_row_keys_and_reason_codes_frozen(tmp_path: Path):
    rec = _record_with_artifacts(tmp_path)
    rows = list(rec.rows)
    assert len(rows) == 1

    row = rows[0]
    assert set(row.keys()) == ROW_KEYS
    reasons = list(row["reason_codes"])
    assert len(reasons) >= 1
    for reason in reasons:
        assert str(reason) in ALLOWED_REASON_CODES


def test_rl01_scope_limits_include_discriminative_candidate(tmp_path: Path):
    rec = _record_with_artifacts(tmp_path)
    limits = set(rec.scope_limits)
    assert "front_door_only" in limits
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
    assert "discriminative_candidate" in limits
    assert "within_rep_only" in limits
    assert "no_external_truth_claim" in limits
