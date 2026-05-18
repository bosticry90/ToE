from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.referent_registry_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID,
    build_result_review,
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
REVIEW_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "referent_registry_result_review_report.py"
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

PROHIBITED_REVIEW_PHRASES = [
    "validated",
    "confirmed",
    "recovered",
    "empirically supported",
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


def test_referent_registry_result_review_files_exist() -> None:
    assert REFERENT_REGISTRY_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_referent_registry_result_review_consumes_registry_and_accepts() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "REFERENT_REGISTRY_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["consumed_registry"]["registry_id"] == "REFERENT_REGISTRY_v0"
    assert review["consumed_registry"]["registry_path"] == "formal/docs/release/REFERENT_REGISTRY_20260515_v0.json"
    assert review["consumed_registry"]["registry_row_count"] == 8
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID


def test_referent_registry_result_review_acceptance_criteria_and_lineage() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    numerical_registry = _json(NUMERICAL_REGISTRY_PATH)
    matrix = _json(MATRIX_PATH)
    protocol = _json(PROTOCOL_PATH)
    referent_registry = _json(REFERENT_REGISTRY_PATH)
    assert _ids(audit, "audit_rows") == EXPECTED_ROWS
    assert _ids(ledger, "ledger_rows") == EXPECTED_ROWS
    assert _ids(numerical_registry, "registry_rows") == EXPECTED_ROWS
    assert _ids(matrix, "matrix_rows") == EXPECTED_ROWS
    assert _ids(protocol, "protocol_rows") == EXPECTED_ROWS
    assert _ids(referent_registry, "referent_rows") == EXPECTED_ROWS
    assert review["source_lineage"]["row_ids_match_prior_lineage"] is True


def test_referent_registry_result_review_preserves_nonclaim_counts_and_unexecuted_comparisons() -> None:
    review = _json(REVIEW_PATH)
    assert review["scope_confirmation"]["promotion_allowed_count"] == 0
    assert review["scope_confirmation"]["all_promotion_allowed_false"] is True
    assert review["scope_confirmation"]["validation_upgrade_count"] == 0
    assert review["scope_confirmation"]["empirical_validation_claim_count"] == 0
    assert review["scope_confirmation"]["referent_comparison_execution_claim_count"] == 0
    assert review["scope_confirmation"]["all_comparison_execution_status_not_executed_v0"] is True
    assert review["scope_confirmation"]["numerical_score_present"] is False
    assert review["referent_gap_confirmation"]["comparison_execution_status_counts"] == {
        "not_executed_v0": 8,
    }
    assert review["referent_gap_confirmation"]["referent_uncertainty_status_counts"] == {
        "not_registered_v0": 8,
    }


def test_referent_registry_result_review_preserves_referent_gap_method_debt_and_uq_limits() -> None:
    review = _json(REVIEW_PATH)
    assert review["referent_gap_confirmation"]["primary_referent_gap"] == (
        "REFERENT_IDENTIFICATION_ALLOWED_USE_AND_UNCERTAINTY_REGISTRATION_INCOMPLETE_V0"
    )
    assert review["referent_gap_confirmation"]["registry_scope"] == (
        "REGISTER_REFERENTS_ONLY_NO_COMPARISON_OR_VALIDATION_EXECUTION_CLAIM"
    )
    assert review["referent_gap_confirmation"]["c6_c7_method_debt_visible"] is True
    assert review["referent_gap_confirmation"]["uq_limitations_visible"] is True
    assert review["referent_gap_confirmation"]["uq_dependency_counts"] == {
        "uq_not_quantified": 5,
        "uq_partial_quantitative": 1,
        "uq_qualitative": 2,
    }


def test_referent_registry_result_review_next_packet_scope() -> None:
    review = _json(REVIEW_PATH)
    assert review["next_packet"] == "SIMULATION_MODEL_CARD_TEMPLATE_v0"
    assert review["next_action"] == "PREPARE_SIMULATION_MODEL_CARD_TEMPLATE_AFTER_REFERENT_REGISTRY_REVIEW"
    assert review["next_packet_authorization_scope"] == "PREPARATION_ONLY"


def test_referent_registry_result_review_forbidden_effects_false_and_no_broad_claim_language() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    review_text = json.dumps(review, sort_keys=True)
    for phrase in PROHIBITED_REVIEW_PHRASES:
        assert phrase not in review_text


def test_referent_registry_result_review_is_deterministic() -> None:
    generated_1 = build_result_review(
        referent_registry_path=REFERENT_REGISTRY_PATH,
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        numerical_registry_path=NUMERICAL_REGISTRY_PATH,
        matrix_path=MATRIX_PATH,
        protocol_path=PROTOCOL_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        referent_registry_path=REFERENT_REGISTRY_PATH,
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        numerical_registry_path=NUMERICAL_REGISTRY_PATH,
        matrix_path=MATRIX_PATH,
        protocol_path=PROTOCOL_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REVIEW_PATH) == generated_1


def test_referent_registry_result_review_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "REFERENT_REGISTRY_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "REFERENT_REGISTRY_RESULT_REVIEW_OUTCOME_v0: "
        "REFERENT_REGISTRY_RESULT_REVIEW_ACCEPTS_NONCLAIM_REFERENT_REGISTRATION_"
        "AND_AUTHORIZES_SIMULATION_MODEL_CARD_TEMPLATE_PREPARATION_ONLY"
    ) in roadmap_text
    assert "SIMULATION_MODEL_CARD_TEMPLATE_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text

    for ref in (
        "REFERENT_REGISTRY_RESULT_REVIEW_v0",
        "formal/docs/release/REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/referent_registry_result_review_report.py",
        "formal/python/tests/test_referent_registry_result_review_gate.py",
        "SIMULATION_MODEL_CARD_TEMPLATE_v0",
        "PREPARE_SIMULATION_MODEL_CARD_TEMPLATE_AFTER_REFERENT_REGISTRY_REVIEW",
    ):
        assert ref in physics_text
