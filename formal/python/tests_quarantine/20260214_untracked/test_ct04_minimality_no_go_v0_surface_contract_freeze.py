from __future__ import annotations

from formal.python.toe.comparators.ct04_minimality_no_go_v0 import (
    ct04_minimality_no_go_v0_record,
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
    "ct04_minimality_ok",
    "ct04_minimality_violation_detected",
    "FAIL_DOMAIN_PARAMETER_INCONSISTENT",
    "FAIL_CFL_BOUND",
    "FAIL_ENERGY_DRIFT_EXCEEDS",
    "FAIL_BREAK_NOT_DETECTED",
    "FAIL_NONDETERMINISTIC_FINGERPRINT",
}


def test_ct04_surface_contract_top_level_keys_frozen():
    rec = ct04_minimality_no_go_v0_record(date="2026-02-09", tolerance_profile="pinned")
    payload = rec.to_jsonable()

    assert payload["schema"] == "CT-04_minimality_no_go_comparator/v0"
    assert payload["observable_id"] == "CT-04"
    assert payload["domain_id"] == "CT-DOMAIN-04"
    assert payload["comparator_role"] == "discriminative_candidate"
    assert payload["tolerance_profile"] == "pinned"
    assert set(payload.keys()) == TOP_LEVEL_KEYS


def test_ct04_surface_contract_row_keys_and_reason_codes_frozen():
    rec = ct04_minimality_no_go_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rows = list(rec.rows)
    assert len(rows) == 2

    for row in rows:
        assert set(row.keys()) == ROW_KEYS
        reasons = list(row["reason_codes"])
        assert len(reasons) >= 1
        for reason in reasons:
            assert str(reason) in ALLOWED_REASON_CODES


def test_ct04_scope_limits_include_discriminative_candidate():
    rec = ct04_minimality_no_go_v0_record(date="2026-02-09", tolerance_profile="pinned")
    limits = set(rec.scope_limits)
    assert "front_door_only" in limits
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
    assert "discriminative_candidate" in limits
    assert "within_rep_only" in limits
    assert "no_external_truth_claim" in limits
