from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.numerical_method_verification_registry_report import (
    DEFAULT_CAPTURED_AT_UTC,
    PREPARATION_RESULT,
    REGISTRY_ID,
    build_registry,
)


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
REVIEW_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_20260515_v0.json"
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_REPORT_v0.md"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "numerical_method_verification_registry_report.py"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

EXPECTED_ROWS = [
    "C6_CP_NLSE_2D_LANE",
    "C7_MT01A_ACOUSTIC_METRIC_LANE",
    "UCFF_SPECTRAL_AUDIT_LINEAGE",
    "BRAGG_DISPERSION_ELIMINATIVE_LANE",
    "RL01_RELATIVISTIC_DISPERSION_LIMIT",
    "RL02_NONRELATIVISTIC_NLSE_LIMIT",
    "GR01_DERIVATION_COMPLETENESS_GATE",
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS",
]

NUMERICAL_METHOD_ROWS = {
    "C6_CP_NLSE_2D_LANE",
    "C7_MT01A_ACOUSTIC_METRIC_LANE",
}

REQUIRED_ROW_FIELDS = [
    "artifact_id",
    "source_ledger_id",
    "source_audit_id",
    "source_artifact_path",
    "method_applicability",
    "equation_or_system_solved",
    "discretization_family",
    "time_integrator",
    "spatial_operator",
    "formal_order_claimed",
    "observed_order_status",
    "convergence_status",
    "exact_solution_benchmark_status",
    "manufactured_solution_status",
    "conservation_diagnostic_status",
    "stability_condition_status",
    "solver_crosscheck_status",
    "failure_modes_registered",
    "verification_depth",
    "validation_status",
    "source_validation_status",
    "validation_status_upgrade_from_ledger",
    "claim_status",
    "source_claim_ceiling",
    "claim_ceiling",
    "method_verification_readout",
    "upgrade_requirements",
    "promotion_allowed",
]

FORBIDDEN_TRUE_KEYS = [
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "phase2_authorization",
    "empirical_validation_claim",
    "seam_closure",
    "master_action_promotion",
    "external_truth_claim",
]

PROHIBITED_PHRASES = [
    "Phase 2 authorized",
    "seam closure authorized",
    "empirical validation complete",
    "theorem discharged by computation",
    "master action promoted",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _ids(payload: dict, key: str) -> list[str]:
    return [row["artifact_id"] for row in payload[key]]


def test_numerical_method_verification_registry_files_exist() -> None:
    assert REGISTRY_PATH.exists()
    assert REPORT_PATH.exists()
    assert TOOL_PATH.exists()


def test_numerical_method_verification_registry_top_level_contract() -> None:
    registry = _json(REGISTRY_PATH)
    assert registry["schema_id"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0"
    assert registry["registry_id"] == REGISTRY_ID
    assert registry["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert registry["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert registry["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert registry["preparation_result"] == PREPARATION_RESULT
    assert registry["consumes_result_review"] == "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_v0"
    assert registry["source_ledger"] == "VVUQ_CREDIBILITY_LEDGER_v0"
    assert registry["source_audit"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
    assert registry["source_audit_row_count"] == 8
    assert registry["row_count"] == 8
    assert registry["method_verification_scope"] == "REGISTER_VERIFICATION_DEPTH_ONLY_NO_COMPLETION_CLAIM"
    assert registry["scoring_policy"] == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0"


def test_numerical_method_verification_registry_rows_match_audit_and_ledger_without_promotion() -> None:
    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    registry = _json(REGISTRY_PATH)
    assert _ids(audit, "audit_rows") == EXPECTED_ROWS
    assert _ids(ledger, "ledger_rows") == EXPECTED_ROWS
    assert _ids(registry, "registry_rows") == EXPECTED_ROWS
    assert registry["promotion_allowed_count"] == 0
    assert registry["all_promotion_allowed_false"] is True
    for row in registry["registry_rows"]:
        assert row["promotion_allowed"] is False
        assert row["claim_ceiling"] == "method_verification_bookkeeping_only"
        assert row["validation_status_upgrade_from_ledger"] is False
        assert "credibility_score" not in row
    assert "credibility_score" not in json.dumps(registry, sort_keys=True)


def test_numerical_method_verification_registry_rows_have_required_method_fields() -> None:
    registry = _json(REGISTRY_PATH)
    allowed_applicability = {
        "numerical_method_applicable",
        "comparator_or_report_surface",
        "formal_or_governance_surface",
        "not_applicable",
    }
    allowed_observed_order = {"not_measured", "measured_partial", "measured_pass", "measured_fail", "not_applicable"}
    allowed_mms = {"not_registered_v0", "candidate", "implemented", "passed", "failed", "not_applicable"}
    allowed_depth = {
        "gated_only",
        "gated_but_not_convergence_verified",
        "convergence_checked",
        "mms_checked",
        "exact_solution_checked",
        "solver_crosschecked",
        "independently_replicated",
        "not_applicable",
    }
    for row in registry["registry_rows"]:
        for field in REQUIRED_ROW_FIELDS:
            assert field in row, f"Missing field {field} in {row.get('artifact_id')}"
        assert row["source_ledger_id"] == "VVUQ_CREDIBILITY_LEDGER_v0"
        assert row["source_audit_id"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
        assert row["method_applicability"] in allowed_applicability
        assert row["observed_order_status"] in allowed_observed_order
        assert row["manufactured_solution_status"] in allowed_mms
        assert row["verification_depth"] in allowed_depth
        assert isinstance(row["failure_modes_registered"], bool)
        assert isinstance(row["upgrade_requirements"], list) and row["upgrade_requirements"]


def test_numerical_method_rows_record_verification_debt_not_completed_verification() -> None:
    registry = _json(REGISTRY_PATH)
    rows_by_id = {row["artifact_id"]: row for row in registry["registry_rows"]}
    for artifact_id in NUMERICAL_METHOD_ROWS:
        row = rows_by_id[artifact_id]
        assert row["method_applicability"] == "numerical_method_applicable"
        assert row["equation_or_system_solved"] != "not_applicable"
        assert row["discretization_family"] != "not_applicable"
        assert row["spatial_operator"] != "not_applicable"
        assert row["observed_order_status"] == "not_measured"
        assert row["convergence_status"] == "not_registered_v0"
        assert row["verification_depth"] == "gated_but_not_convergence_verified"
        assert row["solver_crosscheck_status"] == "not_performed"
        assert row["non_numerical_method_reason"] == ""


def test_non_numerical_rows_explain_why_method_verification_is_not_applicable() -> None:
    registry = _json(REGISTRY_PATH)
    for row in registry["registry_rows"]:
        if row["artifact_id"] in NUMERICAL_METHOD_ROWS:
            continue
        assert row["method_applicability"] in {"comparator_or_report_surface", "formal_or_governance_surface"}
        assert row["non_numerical_method_reason"]
        assert row["equation_or_system_solved"] == "not_applicable"
        assert row["discretization_family"] == "not_applicable"
        assert row["time_integrator"] == "not_applicable"
        assert row["spatial_operator"] == "not_applicable"
        assert row["observed_order_status"] == "not_applicable"
        assert row["convergence_status"] == "not_applicable"
        assert row["manufactured_solution_status"] == "not_applicable"
        assert row["verification_depth"] == "not_applicable"


def test_numerical_method_verification_registry_does_not_upgrade_validation_beyond_vvuq_ledger() -> None:
    ledger = _json(LEDGER_PATH)
    registry = _json(REGISTRY_PATH)
    ledger_by_id = {row["artifact_id"]: row for row in ledger["ledger_rows"]}
    assert registry["validation_upgrade_count"] == 0
    for row in registry["registry_rows"]:
        source = ledger_by_id[row["artifact_id"]]
        assert row["validation_status"] == source["validation_status"]
        assert row["source_validation_status"] == source["validation_status"]
        assert row["claim_status"] == source["claim_status"]
        assert row["source_claim_ceiling"] == source["claim_ceiling"]


def test_numerical_method_verification_registry_forbidden_effects_false_and_no_promotion_language() -> None:
    registry = _json(REGISTRY_PATH)
    forbidden = registry["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(registry, sort_keys=True) + "\n" + _read(REPORT_PATH) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_numerical_method_verification_registry_is_deterministic() -> None:
    generated_1 = build_registry(
        ledger_path=LEDGER_PATH,
        audit_path=AUDIT_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_registry(
        ledger_path=LEDGER_PATH,
        audit_path=AUDIT_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REGISTRY_PATH) == generated_1


def test_numerical_method_verification_registry_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert "NUMERICAL_METHOD_VERIFICATION_REGISTRY_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_STATUS_v0: "
        "ACCEPTED_BOUNDED_NONCLAIM"
    ) in roadmap_text
    assert (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_OUTCOME_v0: "
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_PREPARED_FROM_VVUQ_REVIEW_"
        "WITH_NONCLAIM_METHOD_VERIFICATION_CEILINGS"
    ) in roadmap_text

    for ref in (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0",
        "formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json",
        "formal/docs/paper/NUMERICAL_METHOD_VERIFICATION_REGISTRY_REPORT_v0.md",
        "formal/python/tools/numerical_method_verification_registry_report.py",
        "formal/python/tests/test_numerical_method_verification_registry_gate.py",
        "formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/numerical_method_verification_registry_result_review_report.py",
        "formal/python/tests/test_numerical_method_verification_registry_result_review_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
