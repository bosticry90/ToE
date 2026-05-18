from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.regime_recovery_matrix_report import (
    DEFAULT_CAPTURED_AT_UTC,
    MATRIX_ID,
    PREPARATION_RESULT,
    build_matrix,
)


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json"
)
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_20260515_v0.json"
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "REGIME_RECOVERY_MATRIX_REPORT_v0.md"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "regime_recovery_matrix_report.py"
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
    "source_registry_id",
    "source_audit_id",
    "source_ledger_id",
    "source_artifact_path",
    "regime_recovery_applicability",
    "target_regime",
    "known_limit_or_comparator",
    "source_known_limit_status",
    "matrix_recovery_status",
    "pass_fail_criterion_status",
    "referent_status",
    "method_verification_dependency",
    "source_method_applicability",
    "source_convergence_status",
    "source_manufactured_solution_status",
    "source_solver_crosscheck_status",
    "uq_dependency",
    "validation_status",
    "source_validation_status",
    "validation_status_upgrade_from_source",
    "recovery_completion_claim",
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
    "known limit recovered",
    "recovered complete",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _ids(payload: dict, key: str) -> list[str]:
    return [row["artifact_id"] for row in payload[key]]


def test_regime_recovery_matrix_files_exist() -> None:
    assert MATRIX_PATH.exists()
    assert REPORT_PATH.exists()
    assert TOOL_PATH.exists()


def test_regime_recovery_matrix_top_level_contract() -> None:
    matrix = _json(MATRIX_PATH)
    assert matrix["schema_id"] == "REGIME_RECOVERY_MATRIX_20260515_v0"
    assert matrix["matrix_id"] == MATRIX_ID
    assert matrix["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert matrix["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert matrix["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert matrix["preparation_result"] == PREPARATION_RESULT
    assert matrix["consumes_result_review"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_v0"
    assert matrix["source_registry"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
    assert matrix["source_vvuq_ledger"] == "VVUQ_CREDIBILITY_LEDGER_v0"
    assert matrix["source_audit"] == "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0"
    assert matrix["row_count"] == 8
    assert matrix["primary_regime_gap"] == "KNOWN_LIMIT_PASS_FAIL_CRITERIA_AND_RECOVERY_EVIDENCE_DEPTH_NOT_COMPLETE_V0"
    assert matrix["scoring_policy"] == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0"


def test_regime_recovery_matrix_rows_match_prior_lineage_without_promotion() -> None:
    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    registry = _json(REGISTRY_PATH)
    matrix = _json(MATRIX_PATH)
    assert _ids(audit, "audit_rows") == EXPECTED_ROWS
    assert _ids(ledger, "ledger_rows") == EXPECTED_ROWS
    assert _ids(registry, "registry_rows") == EXPECTED_ROWS
    assert _ids(matrix, "matrix_rows") == EXPECTED_ROWS
    assert matrix["promotion_allowed_count"] == 0
    assert matrix["all_promotion_allowed_false"] is True
    assert matrix["validation_upgrade_count"] == 0
    assert matrix["recovery_completion_claim_count"] == 0
    for row in matrix["matrix_rows"]:
        assert row["promotion_allowed"] is False
        assert row["recovery_completion_claim"] is False
        assert row["validation_status_upgrade_from_source"] is False


def test_regime_recovery_matrix_rows_have_required_fields_and_conservative_statuses() -> None:
    matrix = _json(MATRIX_PATH)
    allowed_applicability = {
        "known_limit_recovery_relevant",
        "regime_comparator_relevant",
        "seam_or_mismatch_relevant",
        "formal_governance_blocked",
        "not_applicable",
    }
    allowed_recovery_status = {"none", "candidate", "partial", "blocked", "not_applicable"}
    allowed_criterion = {"not_registered_v0", "partial", "defined", "blocked", "not_applicable"}
    allowed_referent = {
        "not_registered_v0",
        "analytic_referent_candidate",
        "literature_referent_candidate",
        "empirical_referent_candidate",
        "registered_partial",
        "blocked",
        "not_applicable",
    }
    allowed_claim_ceiling = {
        "internal_consequence_only",
        "known_limit_relevance_only",
        "validation_candidate_only",
        "blocked_no_upgrade",
        "nonclaim_bookkeeping_only",
    }
    prohibited_recovery_values = {"passed", "validated", "confirmed", "complete", "recovered_complete"}

    for row in matrix["matrix_rows"]:
        for field in REQUIRED_ROW_FIELDS:
            assert field in row, f"Missing field {field} in {row.get('artifact_id')}"
        assert row["regime_recovery_applicability"] in allowed_applicability
        assert row["matrix_recovery_status"] in allowed_recovery_status
        assert row["matrix_recovery_status"] not in prohibited_recovery_values
        assert row["pass_fail_criterion_status"] in allowed_criterion
        assert row["referent_status"] in allowed_referent
        assert row["claim_ceiling"] in allowed_claim_ceiling
        assert isinstance(row["upgrade_requirements"], list) and row["upgrade_requirements"]


def test_regime_recovery_matrix_preserves_validation_status_from_registry() -> None:
    registry = _json(REGISTRY_PATH)
    matrix = _json(MATRIX_PATH)
    registry_by_id = {row["artifact_id"]: row for row in registry["registry_rows"]}
    for row in matrix["matrix_rows"]:
        source = registry_by_id[row["artifact_id"]]
        assert row["source_registry_id"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
        assert row["source_ledger_id"] == source["source_ledger_id"]
        assert row["validation_status"] == source["validation_status"]
        assert row["source_validation_status"] == source["validation_status"]
        assert row["source_method_applicability"] == source["method_applicability"]


def test_regime_recovery_matrix_keeps_numerical_method_debt_visible() -> None:
    matrix = _json(MATRIX_PATH)
    rows_by_id = {row["artifact_id"]: row for row in matrix["matrix_rows"]}
    for artifact_id in ("C6_CP_NLSE_2D_LANE", "C7_MT01A_ACOUSTIC_METRIC_LANE"):
        row = rows_by_id[artifact_id]
        assert row["source_method_applicability"] == "numerical_method_applicable"
        assert row["source_convergence_status"] == "not_registered_v0"
        assert row["source_solver_crosscheck_status"] == "not_performed"
        assert row["method_verification_dependency"] == (
            "method_debt_visible_convergence_mms_or_solver_crosscheck_unresolved_v0"
        )


def test_regime_recovery_matrix_forbidden_effects_false_and_no_promotion_language() -> None:
    matrix = _json(MATRIX_PATH)
    forbidden = matrix["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(matrix, sort_keys=True) + "\n" + _read(REPORT_PATH) + "\n" + _read(ROADMAP_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_regime_recovery_matrix_is_deterministic() -> None:
    generated_1 = build_matrix(
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        registry_path=REGISTRY_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_matrix(
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        registry_path=REGISTRY_PATH,
        review_path=REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(MATRIX_PATH) == generated_1


def test_regime_recovery_matrix_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert "REGIME_RECOVERY_MATRIX_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "REGIME_RECOVERY_MATRIX_OUTCOME_v0: "
        "REGIME_RECOVERY_MATRIX_PREPARED_FROM_NUMERICAL_METHOD_REGISTRY_REVIEW_"
        "WITH_NONCLAIM_KNOWN_LIMIT_CEILINGS"
    ) in roadmap_text

    for ref in (
        "REGIME_RECOVERY_MATRIX_v0",
        "formal/docs/release/REGIME_RECOVERY_MATRIX_20260515_v0.json",
        "formal/docs/paper/REGIME_RECOVERY_MATRIX_REPORT_v0.md",
        "formal/python/tools/regime_recovery_matrix_report.py",
        "formal/python/tests/test_regime_recovery_matrix_gate.py",
        "formal/docs/release/REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/regime_recovery_matrix_result_review_report.py",
        "formal/python/tests/test_regime_recovery_matrix_result_review_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
