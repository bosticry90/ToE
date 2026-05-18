from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.vvuq_credibility_ledger_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    OUTCOME_ID,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
AUDIT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json"
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
REVIEW_PATH = REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_20260515_v0.json"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "vvuq_credibility_ledger_result_review_report.py"
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
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _ids(payload: dict, key: str) -> list[str]:
    return [row["artifact_id"] for row in payload[key]]


def test_vvuq_credibility_ledger_result_review_files_exist() -> None:
    assert LEDGER_PATH.exists()
    assert REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_vvuq_credibility_ledger_result_review_consumes_ledger_and_accepts() -> None:
    review = _json(REVIEW_PATH)
    assert review["schema_id"] == "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_20260515_v0"
    assert review["review_id"] == "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_v0"
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["consumed_ledger"]["ledger_id"] == "VVUQ_CREDIBILITY_LEDGER_v0"
    assert review["consumed_ledger"]["ledger_path"] == "formal/docs/release/VVUQ_CREDIBILITY_LEDGER_20260515_v0.json"
    assert review["consumed_ledger"]["ledger_row_count"] == 8
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID


def test_vvuq_credibility_ledger_result_review_acceptance_criteria() -> None:
    review = _json(REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    audit = _json(AUDIT_PATH)
    ledger = _json(LEDGER_PATH)
    assert _ids(audit, "audit_rows") == EXPECTED_ROWS
    assert _ids(ledger, "ledger_rows") == EXPECTED_ROWS
    assert review["scope_confirmation"]["promotion_allowed_count"] == 0
    assert review["scope_confirmation"]["all_promotion_allowed_false"] is True
    assert review["scope_confirmation"]["validation_upgrade_count"] == 0
    assert review["scope_confirmation"]["validation_upgrades"] == []
    assert review["scope_confirmation"]["numerical_score_present"] is False


def test_vvuq_credibility_ledger_result_review_next_packet_is_preparation_only() -> None:
    review = _json(REVIEW_PATH)
    assert review["next_packet"] == "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0"
    assert review["next_action"] == "PREPARE_NUMERICAL_METHOD_VERIFICATION_REGISTRY_AFTER_VVUQ_LEDGER_REVIEW"
    assert review["next_packet_authorization_scope"] == "PREPARATION_ONLY"
    assert review["gap_confirmation"]["primary_gap_pattern"] == (
        "UQ_DEPTH_AND_VALIDATION_DEPTH_ARE_PRIMARY_NEXT_CREDIBILITY_GAPS"
    )


def test_vvuq_credibility_ledger_result_review_forbidden_effects_false_and_no_promotion_language() -> None:
    review = _json(REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(review, sort_keys=True) + "\n" + _read(ROADMAP_PATH) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_vvuq_credibility_ledger_result_review_is_deterministic() -> None:
    generated_1 = build_result_review(
        ledger_path=LEDGER_PATH,
        audit_path=AUDIT_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        ledger_path=LEDGER_PATH,
        audit_path=AUDIT_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert _json(REVIEW_PATH) == generated_1


def test_vvuq_credibility_ledger_result_review_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)

    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_OUTCOME_v0: "
        "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_ACCEPTS_NONCLAIM_CREDIBILITY_BOOKKEEPING_"
        "AND_AUTHORIZES_NUMERICAL_METHOD_VERIFICATION_REGISTRY_PREPARATION_ONLY"
    ) in roadmap_text
    assert "NUMERICAL_METHOD_VERIFICATION_REGISTRY_STATUS_v0: PREPARED_BOUNDED_NONCLAIM" in roadmap_text
    assert "NUMERICAL_METHOD_VERIFICATION_REGISTRY_GATE_v0: formal/python/tests/test_numerical_method_verification_registry_gate.py" in roadmap_text

    for ref in (
        "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_v0",
        "formal/docs/release/VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/vvuq_credibility_ledger_result_review_report.py",
        "formal/python/tests/test_vvuq_credibility_ledger_result_review_gate.py",
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0",
    ):
        assert ref in physics_text
