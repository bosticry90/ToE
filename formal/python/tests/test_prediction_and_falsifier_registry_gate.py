from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prediction_and_falsifier_registry_report import (
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
REFERENT_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_20260515_v0.json"
TEMPLATE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json"
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0.json"
)
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json"
)
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PREDICTION_AND_FALSIFIER_REGISTRY_REPORT_v0.md"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "prediction_and_falsifier_registry_report.py"
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
    "test_design_applicability",
    "prediction_status",
    "falsifier_status",
    "prediction_statement",
    "falsifier_statement",
    "observable_or_quantity",
    "pass_fail_criterion_status",
    "execution_status",
    "referent_dependency",
    "robustness_dependency",
    "method_verification_dependency",
    "uq_dependency",
    "claim_ceiling",
    "prediction_execution_claim",
    "falsifier_execution_claim",
    "prediction_result_claim",
    "falsifier_result_claim",
    "promotion_allowed",
    "upgrade_requirements",
]

FORBIDDEN_TRUE_KEYS = [
    "prediction_execution",
    "falsifier_execution",
    "validation_upgrade",
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
    "prediction confirmed",
    "falsifier passed",
    "model validated",
    "claim promoted",
    "recovered complete",
    "Phase 2 authorized",
    "seam closure authorized",
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


def test_prediction_and_falsifier_registry_files_exist() -> None:
    assert REGISTRY_PATH.exists()
    assert REPORT_PATH.exists()
    assert TOOL_PATH.exists()


def test_prediction_and_falsifier_registry_top_level_contract() -> None:
    registry = _json(REGISTRY_PATH)
    assert registry["schema_id"] == "PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0"
    assert registry["registry_id"] == REGISTRY_ID
    assert registry["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert registry["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert registry["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert registry["preparation_result"] == PREPARATION_RESULT
    assert registry["consumes_result_review"] == "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_v0"
    assert registry["source_model_card_template"] == "SIMULATION_MODEL_CARD_TEMPLATE_v0"
    assert registry["source_referent_registry"] == "REFERENT_REGISTRY_v0"
    assert registry["source_sensitivity_robustness_protocol"] == "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0"
    assert registry["source_regime_recovery_matrix"] == "REGIME_RECOVERY_MATRIX_v0"
    assert registry["source_numerical_method_registry"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
    assert registry["source_vvuq_ledger"] == "VVUQ_CREDIBILITY_LEDGER_v0"
    assert registry["source_audit"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
    assert registry["row_count"] == 8
    assert registry["primary_falsifier_gap"] == (
        "PREDICTION_AND_FALSIFIER_PASS_FAIL_CRITERIA_REGISTERED_BUT_NOT_EXECUTED_V0"
    )
    assert registry["registry_scope"] == "REGISTER_TEST_DESIGNS_ONLY_NO_EXECUTION_OR_RESULT_CLAIM"


def test_prediction_and_falsifier_registry_rows_match_full_lineage() -> None:
    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    numerical_registry = _json(NUMERICAL_REGISTRY_PATH)
    matrix = _json(MATRIX_PATH)
    protocol = _json(PROTOCOL_PATH)
    referent_registry = _json(REFERENT_REGISTRY_PATH)
    registry = _json(REGISTRY_PATH)
    assert _ids(audit, "audit_rows") == EXPECTED_ROWS
    assert _ids(ledger, "ledger_rows") == EXPECTED_ROWS
    assert _ids(numerical_registry, "registry_rows") == EXPECTED_ROWS
    assert _ids(matrix, "matrix_rows") == EXPECTED_ROWS
    assert _ids(protocol, "protocol_rows") == EXPECTED_ROWS
    assert _ids(referent_registry, "referent_rows") == EXPECTED_ROWS
    assert _ids(registry, "registry_rows") == EXPECTED_ROWS


def test_prediction_and_falsifier_registry_has_required_rows_without_execution_or_promotion() -> None:
    registry = _json(REGISTRY_PATH)
    assert registry["prediction_execution_claim_count"] == 0
    assert registry["falsifier_execution_claim_count"] == 0
    assert registry["prediction_result_claim_count"] == 0
    assert registry["falsifier_result_claim_count"] == 0
    assert registry["promotion_allowed_count"] == 0
    assert registry["all_promotion_allowed_false"] is True
    assert registry["validation_upgrade_count"] == 0
    for row in registry["registry_rows"]:
        for field in REQUIRED_ROW_FIELDS:
            assert field in row, f"Missing field {field} in {row.get('artifact_id')}"
        assert row["prediction_status"] == "candidate_not_executed_v0"
        assert row["falsifier_status"] == "defined_not_executed_v0"
        assert row["execution_status"] == "not_executed_v0"
        assert row["pass_fail_criterion_status"] == "not_fully_registered_v0"
        assert row["claim_ceiling"] == "test_design_registration_only"
        assert row["prediction_execution_claim"] is False
        assert row["falsifier_execution_claim"] is False
        assert row["prediction_result_claim"] is False
        assert row["falsifier_result_claim"] is False
        assert row["promotion_allowed"] is False
        assert isinstance(row["upgrade_requirements"], list) and row["upgrade_requirements"]


def test_prediction_and_falsifier_registry_preserves_dependencies_and_debt() -> None:
    registry = _json(REGISTRY_PATH)
    rows_by_id = {row["artifact_id"]: row for row in registry["registry_rows"]}
    for artifact_id in ("C6_CP_NLSE_2D_LANE", "C7_MT01A_ACOUSTIC_METRIC_LANE"):
        row = rows_by_id[artifact_id]
        assert row["method_verification_dependency"] == "method_debt_visible"
        assert row["source_method_applicability"] == "numerical_method_applicable"
        assert row["source_convergence_status"] == "not_registered_v0"
        assert row["source_solver_crosscheck_status"] == "not_performed"
        assert row["uq_dependency"] == "uq_not_quantified"
        assert row["robustness_dependency"] == "robustness_protocol_not_executed"
        assert row["source_scan_execution_status"] == "not_executed_v0"

    assert registry["summary"]["uq_dependency_counts"] == {
        "uq_not_quantified": 5,
        "uq_partial_quantitative": 1,
        "uq_qualitative": 2,
    }
    assert registry["summary"]["robustness_dependency_counts"] == {"robustness_protocol_not_executed": 8}
    assert registry["summary"]["execution_status_counts"] == {"not_executed_v0": 8}
    assert registry["summary"]["pass_fail_criterion_status_counts"] == {"not_fully_registered_v0": 8}


def test_prediction_and_falsifier_registry_forbidden_effects_false_and_no_result_language() -> None:
    registry = _json(REGISTRY_PATH)
    forbidden = registry["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(registry, sort_keys=True) + "\n" + _read(REPORT_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_prediction_and_falsifier_registry_is_deterministic() -> None:
    generated_1 = build_registry(
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        numerical_registry_path=NUMERICAL_REGISTRY_PATH,
        matrix_path=MATRIX_PATH,
        protocol_path=PROTOCOL_PATH,
        referent_registry_path=REFERENT_REGISTRY_PATH,
        template_path=TEMPLATE_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_registry(
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        numerical_registry_path=NUMERICAL_REGISTRY_PATH,
        matrix_path=MATRIX_PATH,
        protocol_path=PROTOCOL_PATH,
        referent_registry_path=REFERENT_REGISTRY_PATH,
        template_path=TEMPLATE_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REGISTRY_PATH) == generated_1


def test_prediction_and_falsifier_registry_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert "PREDICTION_AND_FALSIFIER_REGISTRY_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert (
        "PREDICTION_AND_FALSIFIER_REGISTRY_OUTCOME_v0: "
        "PREDICTION_AND_FALSIFIER_REGISTRY_PREPARED_FROM_MODEL_CARD_TEMPLATE_REVIEW_"
        "WITH_NONCLAIM_TEST_DESIGN_CEILINGS"
    ) in roadmap_text

    for ref in (
        "PREDICTION_AND_FALSIFIER_REGISTRY_v0",
        "formal/docs/release/PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json",
        "formal/docs/paper/PREDICTION_AND_FALSIFIER_REGISTRY_REPORT_v0.md",
        "formal/python/tools/prediction_and_falsifier_registry_report.py",
        "formal/python/tests/test_prediction_and_falsifier_registry_gate.py",
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
