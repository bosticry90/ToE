from formal.python.toe.comparators.cv02_bec_bragg_b1_v0 import cv02_bec_bragg_b1_v0_record


EXPECTED_TOP_LEVEL_KEYS = {
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

EXPECTED_ROW_KEYS = {
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


def test_cv02_surface_contract_top_level_keys_frozen():
    rec = cv02_bec_bragg_b1_v0_record(date="2026-02-08")
    payload = rec.to_jsonable()

    assert set(payload.keys()) == EXPECTED_TOP_LEVEL_KEYS
    assert payload["schema"] == "OV-CV-02_bec_bragg_b1_comparator/v1"
    assert payload["observable_id"] == "OV-CV-02"
    assert payload["domain_id"] == "DRBR-DOMAIN-02"


def test_cv02_surface_contract_rows_and_reason_codes_frozen():
    rec = cv02_bec_bragg_b1_v0_record(date="2026-02-08")

    assert len(rec.rows) == 2
    for row in rec.rows:
        assert set(row.keys()) == EXPECTED_ROW_KEYS

        reasons = list(row.get("reason_codes") or [])
        assert len(reasons) >= 1
        for reason in reasons:
            assert str(reason) in ALLOWED_REASON_CODES


def test_cv02_scope_limits_include_integrity_only():
    rec = cv02_bec_bragg_b1_v0_record(date="2026-02-08")

    limits = set(rec.scope_limits)
    required = {
        "front_door_only",
        "typed_artifacts_only",
        "deterministic_record_only",
        "integrity_only",
        "no_external_truth_claim",
    }
    assert required.issubset(limits)
