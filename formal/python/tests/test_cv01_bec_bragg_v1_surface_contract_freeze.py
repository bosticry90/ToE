from formal.python.toe.comparators.cv01_bec_bragg_v1 import cv01_bec_bragg_v1_record


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
    "cross_artifact",
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

CROSS_KEYS = {
    "check_id",
    "input_fingerprints",
    "input_data_fingerprints",
    "speed_linear",
    "speed_curved",
    "speed_residual",
    "tolerance",
    "passed",
    "reason_codes",
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
    "cv01_v1_cross_artifact_speed_consistent",
    "cv01_fail_linear_vs_curved_speed_inconsistent",
    "cv01_fail_cross_artifact_nonpositive_speed",
}


def test_cv01_v1_surface_contract_top_level_keys_frozen():
    rec = cv01_bec_bragg_v1_record(date="2026-02-08", tolerance_profile="pinned")
    payload = rec.to_jsonable()

    assert payload["schema"] == "OV-CV-01_bec_bragg_v1_comparator/v1"
    assert payload["observable_id"] == "OV-CV-01"
    assert payload["domain_id"] == "DRBR-DOMAIN-01"
    assert payload["comparator_role"] == "discriminative_candidate"
    assert payload["tolerance_profile"] == "pinned"
    assert set(payload.keys()) == TOP_LEVEL_KEYS


def test_cv01_v1_surface_contract_rows_cross_and_reason_codes_frozen():
    rec = cv01_bec_bragg_v1_record(date="2026-02-08", tolerance_profile="pinned")
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

    cross = dict(rec.cross_artifact)
    assert set(cross.keys()) == CROSS_KEYS
    assert cross["check_id"] == "linear_vs_curved_speed_residual"
    cross_reasons = list(cross["reason_codes"])
    assert len(cross_reasons) >= 1
    for reason in cross_reasons:
        assert str(reason) in ALLOWED_REASON_CODES


def test_cv01_v1_scope_limits_include_discriminative_candidate():
    rec = cv01_bec_bragg_v1_record(date="2026-02-08", tolerance_profile="pinned")
    limits = set(rec.scope_limits)
    assert "front_door_only" in limits
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
    assert "discriminative_candidate" in limits
    assert "no_external_truth_claim" in limits
