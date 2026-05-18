from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.sensitivity_robustness_protocol_report import (
    DEFAULT_CAPTURED_AT_UTC,
    PREPARATION_RESULT,
    PROTOCOL_ID,
    build_protocol,
)


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_20260515_v0.json"
REVIEW_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0.json"
PROTOCOL_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json"
)
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "SENSITIVITY_ROBUSTNESS_PROTOCOL_REPORT_v0.md"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "sensitivity_robustness_protocol_report.py"
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
    "source_matrix_id",
    "source_registry_id",
    "source_ledger_id",
    "source_audit_id",
    "source_artifact_path",
    "robustness_applicability",
    "required_scans",
    "current_robustness_status",
    "scan_execution_status",
    "failure_envelope_status",
    "sensitivity_ranking_status",
    "confidence_label_status",
    "method_verification_dependency",
    "source_method_applicability",
    "source_convergence_status",
    "source_solver_crosscheck_status",
    "uq_dependency",
    "source_recovery_status",
    "validation_status",
    "source_validation_status",
    "validation_status_upgrade_from_source",
    "robustness_completion_claim",
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
    "robustness demonstrated",
    "robustness complete",
    "scan executed",
    "scans executed",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _ids(payload: dict, key: str) -> list[str]:
    return [row["artifact_id"] for row in payload[key]]


def test_sensitivity_robustness_protocol_files_exist() -> None:
    assert PROTOCOL_PATH.exists()
    assert REPORT_PATH.exists()
    assert TOOL_PATH.exists()


def test_sensitivity_robustness_protocol_top_level_contract() -> None:
    protocol = _json(PROTOCOL_PATH)
    assert protocol["schema_id"] == "SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0"
    assert protocol["protocol_id"] == PROTOCOL_ID
    assert protocol["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert protocol["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert protocol["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert protocol["preparation_result"] == PREPARATION_RESULT
    assert protocol["consumes_result_review"] == "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_v0"
    assert protocol["source_matrix"] == "REGIME_RECOVERY_MATRIX_v0"
    assert protocol["source_registry"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
    assert protocol["source_vvuq_ledger"] == "VVUQ_CREDIBILITY_LEDGER_v0"
    assert protocol["source_audit"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
    assert protocol["row_count"] == 8
    assert protocol["primary_robustness_gap"] == (
        "PERTURBATION_RESOLUTION_SOLVER_TOLERANCE_AND_FAILURE_ENVELOPE_PROTOCOL_NOT_EXECUTED_V0"
    )
    assert protocol["protocol_scope"] == "DEFINE_ROBUSTNESS_REQUIREMENTS_ONLY_NO_SCAN_EXECUTION_CLAIM"


def test_sensitivity_robustness_protocol_rows_match_prior_lineage_without_promotion_or_completion() -> None:
    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    registry = _json(REGISTRY_PATH)
    matrix = _json(MATRIX_PATH)
    protocol = _json(PROTOCOL_PATH)
    assert _ids(audit, "audit_rows") == EXPECTED_ROWS
    assert _ids(ledger, "ledger_rows") == EXPECTED_ROWS
    assert _ids(registry, "registry_rows") == EXPECTED_ROWS
    assert _ids(matrix, "matrix_rows") == EXPECTED_ROWS
    assert _ids(protocol, "protocol_rows") == EXPECTED_ROWS
    assert protocol["promotion_allowed_count"] == 0
    assert protocol["all_promotion_allowed_false"] is True
    assert protocol["validation_upgrade_count"] == 0
    assert protocol["robustness_completion_claim_count"] == 0
    assert protocol["scan_execution_claim_count"] == 0
    for row in protocol["protocol_rows"]:
        assert row["promotion_allowed"] is False
        assert row["robustness_completion_claim"] is False
        assert row["validation_status_upgrade_from_source"] is False
        assert row["scan_execution_status"] == "not_executed_v0"


def test_sensitivity_robustness_protocol_rows_have_required_fields_and_scan_obligations() -> None:
    protocol = _json(PROTOCOL_PATH)
    allowed_applicability = {
        "simulation_or_numerical_method_surface",
        "comparator_or_report_surface",
        "formal_governance_surface",
        "seam_or_mismatch_report_surface",
    }
    allowed_uq = {"uq_not_quantified", "uq_qualitative", "uq_partial_quantitative", "uq_quantitative"}
    for row in protocol["protocol_rows"]:
        for field in REQUIRED_ROW_FIELDS:
            assert field in row, f"Missing field {field} in {row.get('artifact_id')}"
        assert row["robustness_applicability"] in allowed_applicability
        assert isinstance(row["required_scans"], list) and row["required_scans"]
        assert row["failure_envelope_status"] == "not_registered_v0"
        assert row["sensitivity_ranking_status"] == "not_registered_v0"
        assert row["confidence_label_status"] == "not_registered_v0"
        assert row["uq_dependency"] in allowed_uq
        assert row["claim_ceiling"] == "robustness_protocol_bookkeeping_only"
        assert isinstance(row["upgrade_requirements"], list) and row["upgrade_requirements"]


def test_sensitivity_robustness_protocol_preserves_method_debt_and_uq_limits() -> None:
    protocol = _json(PROTOCOL_PATH)
    rows_by_id = {row["artifact_id"]: row for row in protocol["protocol_rows"]}
    for artifact_id in ("C6_CP_NLSE_2D_LANE", "C7_MT01A_ACOUSTIC_METRIC_LANE"):
        row = rows_by_id[artifact_id]
        assert row["robustness_applicability"] == "simulation_or_numerical_method_surface"
        assert row["method_verification_dependency"] == "method_debt_visible"
        assert row["source_method_applicability"] == "numerical_method_applicable"
        assert row["source_convergence_status"] == "not_registered_v0"
        assert row["source_solver_crosscheck_status"] == "not_performed"
        assert row["uq_dependency"] == "uq_not_quantified"
        assert "resolution_perturbation" in row["required_scans"]
        assert "solver_tolerance_perturbation" in row["required_scans"]

    uq_counts = protocol["summary"]["uq_dependency_counts"]
    assert uq_counts["uq_not_quantified"] == 5
    assert uq_counts["uq_qualitative"] == 2
    assert uq_counts["uq_partial_quantitative"] == 1


def test_sensitivity_robustness_protocol_forbidden_effects_false_and_no_completion_language() -> None:
    protocol = _json(PROTOCOL_PATH)
    forbidden = protocol["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(protocol, sort_keys=True) + "\n" + _read(REPORT_PATH) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_sensitivity_robustness_protocol_is_deterministic() -> None:
    generated_1 = build_protocol(
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        registry_path=REGISTRY_PATH,
        matrix_path=MATRIX_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_protocol(
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        registry_path=REGISTRY_PATH,
        matrix_path=MATRIX_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(PROTOCOL_PATH) == generated_1


def test_sensitivity_robustness_protocol_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert "SENSITIVITY_ROBUSTNESS_PROTOCOL_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert (
        "SENSITIVITY_ROBUSTNESS_PROTOCOL_OUTCOME_v0: "
        "SENSITIVITY_ROBUSTNESS_PROTOCOL_PREPARED_FROM_REGIME_RECOVERY_REVIEW_"
        "WITH_NONCLAIM_ROBUSTNESS_CEILINGS"
    ) in roadmap_text

    for ref in (
        "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0",
        "formal/docs/release/SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json",
        "formal/docs/paper/SENSITIVITY_ROBUSTNESS_PROTOCOL_REPORT_v0.md",
        "formal/python/tools/sensitivity_robustness_protocol_report.py",
        "formal/python/tests/test_sensitivity_robustness_protocol_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
