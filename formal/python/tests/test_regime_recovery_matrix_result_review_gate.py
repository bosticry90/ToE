from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.regime_recovery_matrix_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json"
)
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_20260515_v0.json"
REVIEW_PATH = REPO_ROOT / "formal" / "docs" / "release" / "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0.json"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "regime_recovery_matrix_result_review_report.py"
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


def test_regime_recovery_matrix_result_review_files_exist() -> None:
    assert MATRIX_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_regime_recovery_matrix_result_review_consumes_matrix_and_accepts() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["consumed_matrix"]["matrix_id"] == "REGIME_RECOVERY_MATRIX_v0"
    assert review["consumed_matrix"]["matrix_path"] == "formal/docs/release/REGIME_RECOVERY_MATRIX_20260515_v0.json"
    assert review["consumed_matrix"]["matrix_row_count"] == 8
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID


def test_regime_recovery_matrix_result_review_acceptance_criteria_and_lineage() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    registry = _json(REGISTRY_PATH)
    matrix = _json(MATRIX_PATH)
    assert _ids(audit, "audit_rows") == EXPECTED_ROWS
    assert _ids(ledger, "ledger_rows") == EXPECTED_ROWS
    assert _ids(registry, "registry_rows") == EXPECTED_ROWS
    assert _ids(matrix, "matrix_rows") == EXPECTED_ROWS
    assert review["source_lineage"]["row_ids_match_prior_lineage"] is True


def test_regime_recovery_matrix_result_review_preserves_nonclaim_counts_and_statuses() -> None:
    review = _json(REVIEW_PATH)
    assert review["scope_confirmation"]["promotion_allowed_count"] == 0
    assert review["scope_confirmation"]["all_promotion_allowed_false"] is True
    assert review["scope_confirmation"]["validation_upgrade_count"] == 0
    assert review["scope_confirmation"]["recovery_completion_claim_count"] == 0
    assert review["scope_confirmation"]["numerical_score_present"] is False
    assert review["scope_confirmation"]["nonconservative_recovery_statuses"] == []
    assert review["regime_gap_confirmation"]["matrix_recovery_status_counts"] == {
        "blocked": 1,
        "candidate": 3,
        "not_applicable": 1,
        "partial": 3,
    }
    assert review["regime_gap_confirmation"]["primary_regime_gap"] == (
        "KNOWN_LIMIT_PASS_FAIL_CRITERIA_AND_RECOVERY_EVIDENCE_DEPTH_NOT_COMPLETE_V0"
    )


def test_regime_recovery_matrix_result_review_preserves_method_debt_and_next_packet_scope() -> None:
    review = _json(REVIEW_PATH)
    assert review["regime_gap_confirmation"]["c6_c7_method_debt_visible"] is True
    assert review["next_packet"] == "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0"
    assert review["next_action"] == "PREPARE_SENSITIVITY_ROBUSTNESS_PROTOCOL_AFTER_REGIME_RECOVERY_MATRIX_REVIEW"
    assert review["next_packet_authorization_scope"] == "PREPARATION_ONLY"


def test_regime_recovery_matrix_result_review_forbidden_effects_false_and_no_completion_language() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(ROADMAP_PATH) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_regime_recovery_matrix_result_review_is_deterministic() -> None:
    generated_1 = build_result_review(
        matrix_path=MATRIX_PATH,
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        registry_path=REGISTRY_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        matrix_path=MATRIX_PATH,
        audit_path=AUDIT_PATH,
        ledger_path=LEDGER_PATH,
        registry_path=REGISTRY_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REVIEW_PATH) == generated_1


def test_regime_recovery_matrix_result_review_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_OUTCOME_v0: "
        "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_ACCEPTS_NONCLAIM_KNOWN_LIMIT_BOOKKEEPING_"
        "AND_AUTHORIZES_SENSITIVITY_ROBUSTNESS_PROTOCOL_PREPARATION_ONLY"
    ) in roadmap_text
    assert "SENSITIVITY_ROBUSTNESS_PROTOCOL_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert "SENSITIVITY_ROBUSTNESS_PROTOCOL_GATE_v0: formal/python/tests/test_sensitivity_robustness_protocol_gate.py" in roadmap_text

    for ref in (
        "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_v0",
        "formal/docs/release/REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/regime_recovery_matrix_result_review_report.py",
        "formal/python/tests/test_regime_recovery_matrix_result_review_gate.py",
        "formal/docs/release/SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json",
        "formal/python/tools/sensitivity_robustness_protocol_report.py",
        "formal/python/tests/test_sensitivity_robustness_protocol_gate.py",
        "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0",
    ):
        assert ref in physics_text
