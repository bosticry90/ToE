from formal.python.toe.comparators.cv01_bec_bragg_v0 import cv01_bec_bragg_v0_record


TOP_LEVEL_KEYS = {
    "schema",
    "date",
    "observable_id",
    "domain_id",
    "comparator_role",
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
    "cv01_metric_constraints_satisfied",
    "cv01_fail_nonpositive_cs2",
    "cv01_fail_metric_signature_identity",
    "cv01_fail_nonunit_gxx",
    "cv01_fail_nonpositive_declared_cs",
    "cv01_fail_declared_vs_metric_cs_mismatch",
    "cv01_fail_nonpositive_declared_c0",
    "cv01_fail_declared_vs_metric_c0_mismatch",
}


def test_cv01_v0_surface_contract_top_level_keys_frozen():
    rec = cv01_bec_bragg_v0_record(date="2026-02-08")
    payload = rec.to_jsonable()

    assert payload["schema"] == "OV-CV-01_bec_bragg_v0_comparator/v1"
    assert payload["observable_id"] == "OV-CV-01"
    assert payload["domain_id"] == "DRBR-DOMAIN-01"
    assert payload["comparator_role"] == "integrity_only"
    assert set(payload.keys()) == TOP_LEVEL_KEYS


def test_cv01_v0_surface_contract_rows_and_reason_codes_frozen():
    rec = cv01_bec_bragg_v0_record(date="2026-02-08")
    rows = list(rec.rows)
    assert len(rows) == 2

    artifact_ids = {str(r["artifact_id"]) for r in rows}
    assert artifact_ids == {"DR01_LINEAR", "DR01_CURVED"}

    for row in rows:
        assert set(row.keys()) == ROW_KEYS
        reasons = list(row["reason_codes"])
        assert len(reasons) >= 1
        for reason in reasons:
            assert str(reason) in ALLOWED_REASON_CODES


def test_cv01_v0_scope_limits_include_integrity_only():
    rec = cv01_bec_bragg_v0_record(date="2026-02-08")
    limits = set(rec.scope_limits)
    assert "front_door_only" in limits
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
    assert "integrity_only" in limits
    assert "no_external_truth_claim" in limits
