from formal.python.toe.comparators.cv03_ucff_dispersion_v1 import cv03_ucff_dispersion_v1_record


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
    "cv03_dispersion_constraints_satisfied",
    "FAIL_DISPERSION_SHAPE_MISMATCH",
    "FAIL_DISPERSION_SIGN",
    "FAIL_DISPERSION_MONOTONICITY",
    "FAIL_K_GRID_ORDER",
    "FAIL_K_GRID_ALIGNMENT",
    "FAIL_DISPERSION_NONDETERMINISTIC",
}


def test_cv03_surface_contract_top_level_keys_frozen():
    rec = cv03_ucff_dispersion_v1_record(date="2026-02-08", tolerance_profile="pinned")
    payload = rec.to_jsonable()

    assert payload["schema"] == "OV-CV-03_ucff_dispersion_comparator/v1"
    assert payload["observable_id"] == "OV-CV-03"
    assert payload["domain_id"] == "DRBR-DOMAIN-UCFF-01"
    assert payload["comparator_role"] == "discriminative_candidate"
    assert payload["tolerance_profile"] == "pinned"
    assert set(payload.keys()) == TOP_LEVEL_KEYS


def test_cv03_surface_contract_row_keys_and_reason_codes_frozen():
    rec = cv03_ucff_dispersion_v1_record(date="2026-02-08", tolerance_profile="pinned")
    rows = list(rec.rows)
    assert len(rows) == 1

    row = rows[0]
    assert set(row.keys()) == ROW_KEYS
    reasons = list(row["reason_codes"])
    assert len(reasons) >= 1
    for reason in reasons:
        assert str(reason) in ALLOWED_REASON_CODES


def test_cv03_scope_limits_include_discriminative_candidate():
    rec = cv03_ucff_dispersion_v1_record(date="2026-02-08", tolerance_profile="pinned")
    limits = set(rec.scope_limits)
    assert "front_door_only" in limits
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
    assert "discriminative_candidate" in limits
    assert "no_external_truth_claim" in limits
