from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.referent_registry_report import (
    DEFAULT_CAPTURED_AT_UTC,
    PREPARATION_RESULT,
    REGISTRY_ID,
    build_registry,
)


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
NUMERICAL_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_20260515_v0.json"
PROTOCOL_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_20260515_v0.json"
)
REFERENT_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_20260515_v0.json"
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "REFERENT_REGISTRY_REPORT_v0.md"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "referent_registry_report.py"
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

REQUIRED_ROW_FIELDS = [
    "artifact_id",
    "source_protocol_id",
    "source_matrix_id",
    "source_registry_id",
    "source_ledger_id",
    "source_audit_id",
    "source_artifact_path",
    "referent_applicability",
    "target_quantity",
    "referent_type",
    "referent_status",
    "allowed_use",
    "comparison_execution_status",
    "referent_uncertainty_status",
    "source_recovery_status",
    "source_robustness_status",
    "method_verification_dependency",
    "source_method_applicability",
    "source_convergence_status",
    "source_solver_crosscheck_status",
    "uq_dependency",
    "source_results_uncertainty",
    "validation_status",
    "source_validation_status",
    "validation_status_upgrade_from_source",
    "empirical_validation_claim",
    "referent_comparison_execution_claim",
    "promotion_allowed",
    "claim_ceiling",
    "upgrade_requirements",
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
    "validated",
    "confirmed",
    "recovered",
    "empirically supported",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _ids(payload: dict, key: str) -> list[str]:
    return [row["artifact_id"] for row in payload[key]]


def test_referent_registry_files_exist() -> None:
    assert REFERENT_REGISTRY_PATH.exists()
    assert REPORT_PATH.exists()
    assert TOOL_PATH.exists()


def test_referent_registry_top_level_contract() -> None:
    registry = _json(REFERENT_REGISTRY_PATH)
    assert registry["schema_id"] == "REFERENT_REGISTRY_20260515_v0"
    assert registry["registry_id"] == REGISTRY_ID
    assert registry["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert registry["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert registry["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert registry["preparation_result"] == PREPARATION_RESULT
    assert registry["consumes_result_review"] == "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_v0"
    assert registry["source_protocol"] == "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0"
    assert registry["source_matrix"] == "REGIME_RECOVERY_MATRIX_v0"
    assert registry["source_registry"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
    assert registry["source_vvuq_ledger"] == "VVUQ_CREDIBILITY_LEDGER_v0"
    assert registry["source_audit"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
    assert registry["row_count"] == 8
    assert registry["primary_referent_gap"] == (
        "REFERENT_IDENTIFICATION_ALLOWED_USE_AND_UNCERTAINTY_REGISTRATION_INCOMPLETE_V0"
    )
    assert registry["registry_scope"] == "REGISTER_REFERENTS_ONLY_NO_COMPARISON_OR_VALIDATION_EXECUTION_CLAIM"


def test_referent_registry_rows_match_prior_lineage_without_promotion_or_execution() -> None:
    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    numerical_registry = _json(NUMERICAL_REGISTRY_PATH)
    matrix = _json(MATRIX_PATH)
    protocol = _json(PROTOCOL_PATH)
    registry = _json(REFERENT_REGISTRY_PATH)
    assert _ids(audit, "audit_rows") == EXPECTED_ROWS
    assert _ids(ledger, "ledger_rows") == EXPECTED_ROWS
    assert _ids(numerical_registry, "registry_rows") == EXPECTED_ROWS
    assert _ids(matrix, "matrix_rows") == EXPECTED_ROWS
    assert _ids(protocol, "protocol_rows") == EXPECTED_ROWS
    assert _ids(registry, "referent_rows") == EXPECTED_ROWS
    assert registry["promotion_allowed_count"] == 0
    assert registry["all_promotion_allowed_false"] is True
    assert registry["validation_upgrade_count"] == 0
    assert registry["referent_comparison_execution_claim_count"] == 0
    assert registry["empirical_validation_claim_count"] == 0
    for row in registry["referent_rows"]:
        assert row["promotion_allowed"] is False
        assert row["validation_status_upgrade_from_source"] is False
        assert row["empirical_validation_claim"] is False
        assert row["referent_comparison_execution_claim"] is False
        assert row["comparison_execution_status"] == "not_executed_v0"


def test_referent_registry_rows_have_required_fields_and_referent_obligations() -> None:
    registry = _json(REFERENT_REGISTRY_PATH)
    allowed_applicability = {
        "simulation_internal_or_analytic_referent_relevant",
        "structural_or_internal_referent_relevant",
        "empirical_or_literature_comparator_relevant",
        "known_limit_or_literature_referent_relevant",
        "formal_governance_referent_blocked",
        "seam_or_mismatch_referent_relevant",
    }
    for row in registry["referent_rows"]:
        for field in REQUIRED_ROW_FIELDS:
            assert field in row, f"Missing field {field} in {row.get('artifact_id')}"
        assert row["referent_applicability"] in allowed_applicability
        assert row["referent_type"].endswith("_candidate")
        assert row["allowed_use"].endswith("_only")
        assert row["referent_uncertainty_status"] == "not_registered_v0"
        assert row["claim_ceiling"] == "referent_registration_only"
        assert isinstance(row["upgrade_requirements"], list) and row["upgrade_requirements"]


def test_referent_registry_preserves_method_debt_and_uq_limits() -> None:
    registry = _json(REFERENT_REGISTRY_PATH)
    rows_by_id = {row["artifact_id"]: row for row in registry["referent_rows"]}
    for artifact_id in ("C6_CP_NLSE_2D_LANE", "C7_MT01A_ACOUSTIC_METRIC_LANE"):
        row = rows_by_id[artifact_id]
        assert row["method_verification_dependency"] == "method_debt_visible"
        assert row["source_method_applicability"] == "numerical_method_applicable"
        assert row["source_convergence_status"] == "not_registered_v0"
        assert row["source_solver_crosscheck_status"] == "not_performed"
        assert row["uq_dependency"] == "uq_not_quantified"

    uq_counts = registry["summary"]["uq_dependency_counts"]
    assert uq_counts["uq_not_quantified"] == 5
    assert uq_counts["uq_qualitative"] == 2
    assert uq_counts["uq_partial_quantitative"] == 1
    assert registry["summary"]["comparison_execution_status_counts"] == {"not_executed_v0": 8}
    assert registry["summary"]["referent_uncertainty_status_counts"] == {"not_registered_v0": 8}


def test_referent_registry_forbidden_effects_false_and_no_comparison_or_validation_language() -> None:
    registry = _json(REFERENT_REGISTRY_PATH)
    forbidden = registry["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(registry, sort_keys=True) + "\n" + _read(REPORT_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_referent_registry_is_deterministic() -> None:
    generated_1 = build_registry(
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        registry_path=NUMERICAL_REGISTRY_PATH,
        matrix_path=MATRIX_PATH,
        protocol_path=PROTOCOL_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_registry(
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        registry_path=NUMERICAL_REGISTRY_PATH,
        matrix_path=MATRIX_PATH,
        protocol_path=PROTOCOL_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REFERENT_REGISTRY_PATH) == generated_1


def test_referent_registry_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert "REFERENT_REGISTRY_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert (
        "REFERENT_REGISTRY_OUTCOME_v0: "
        "REFERENT_REGISTRY_PREPARED_FROM_SENSITIVITY_ROBUSTNESS_REVIEW_"
        "WITH_NONCLAIM_REFERENT_CEILINGS"
    ) in roadmap_text

    for ref in (
        "REFERENT_REGISTRY_v0",
        "formal/docs/release/REFERENT_REGISTRY_20260515_v0.json",
        "formal/docs/paper/REFERENT_REGISTRY_REPORT_v0.md",
        "formal/python/tools/referent_registry_report.py",
        "formal/python/tests/test_referent_registry_gate.py",
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
