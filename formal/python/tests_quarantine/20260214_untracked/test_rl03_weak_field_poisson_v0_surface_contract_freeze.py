from __future__ import annotations

from formal.python.toe.comparators.rl03_weak_field_poisson_v0 import rl03_weak_field_poisson_v0_record


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
    "rl03_weak_field_poisson_constraints_satisfied",
    "FAIL_X_GRID_ORDER",
    "FAIL_X_GRID_ALIGNMENT",
    "FAIL_DOMAIN_PARAMETER_INCONSISTENT",
    "FAIL_GAUGE_CONSTRAINT",
    "FAIL_POISSON_RESIDUAL",
    "FAIL_NONDETERMINISTIC_FINGERPRINT",
}


def test_rl03_surface_contract_top_level_keys_frozen():
    rec = rl03_weak_field_poisson_v0_record(date="2026-02-09", tolerance_profile="pinned")
    payload = rec.to_jsonable()

    assert payload["schema"] == "OV-RL-03_weak_field_poisson_comparator/v0"
    assert payload["observable_id"] == "OV-RL-03"
    assert payload["domain_id"] == "DRBR-DOMAIN-RL-03"
    assert payload["comparator_role"] == "discriminative_candidate"
    assert payload["tolerance_profile"] == "pinned"
    assert set(payload.keys()) == TOP_LEVEL_KEYS


def test_rl03_surface_contract_row_keys_and_reason_codes_frozen():
    rec = rl03_weak_field_poisson_v0_record(date="2026-02-09", tolerance_profile="pinned")
    rows = list(rec.rows)
    assert len(rows) == 1

    row = rows[0]
    assert set(row.keys()) == ROW_KEYS
    reasons = list(row["reason_codes"])
    assert len(reasons) >= 1
    for reason in reasons:
        assert str(reason) in ALLOWED_REASON_CODES


def test_rl03_scope_limits_include_discriminative_candidate():
    rec = rl03_weak_field_poisson_v0_record(date="2026-02-09", tolerance_profile="pinned")
    limits = set(rec.scope_limits)
    assert "front_door_only" in limits
    assert "typed_artifacts_only" in limits
    assert "deterministic_record_only" in limits
    assert "discriminative_candidate" in limits
    assert "within_rep_only" in limits
    assert "no_external_truth_claim" in limits
