from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.computational_physics_integration_closeout_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXPECTED_ROWS,
    PACKET_PATHS,
    PREPARATION_RESULT,
    build_closeout,
)


REPO_ROOT = find_repo_root(Path(__file__))
CLOSEOUT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0.json"
)
REPORT_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_REPORT_v0.md"
TOOL_PATH = (
    REPO_ROOT / "formal" / "python" / "tools" / "computational_physics_integration_closeout_report.py"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"

PROHIBITED_PHRASES = [
    "theory validation complete",
    "empirical validation complete",
    "referent comparison executed",
    "robustness scan executed",
    "prediction confirmed",
    "falsifier passed",
    "falsifier succeeded",
    "model validated",
    "claim promoted",
    "empirically supported",
    "recovered complete",
    "Phase 2 authorized",
    "seam closure authorized",
    "theorem discharged by computation",
    "master action promoted",
]

FORBIDDEN_TRUE_KEYS = [
    "theory_validation",
    "empirical_validation",
    "referent_comparison_execution",
    "robustness_scan_execution",
    "prediction_execution",
    "falsifier_execution",
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "seam_closure",
    "phase2_authorization",
    "master_action_promotion",
    "simulation_execution",
    "validation_upgrade",
    "claim_promotion",
    "numerical_credibility_scoring",
    "external_truth_claim",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_computational_physics_integration_closeout_files_exist() -> None:
    assert CLOSEOUT_PATH.exists()
    assert REPORT_PATH.exists()
    assert TOOL_PATH.exists()
    for path in PACKET_PATHS.values():
        assert path.exists(), f"Missing stack packet: {path}"


def test_computational_physics_integration_closeout_top_level_contract() -> None:
    closeout = _json(CLOSEOUT_PATH)
    assert closeout["schema_id"] == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0"
    assert closeout["closeout_id"] == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0"
    assert closeout["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert closeout["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert closeout["authorization_class"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert closeout["preparation_result"] == PREPARATION_RESULT
    assert closeout["consumes_result_review"] == "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_v0"
    assert closeout["consumes_result_review_pointer"] == (
        "formal/docs/release/PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_20260515_v0.json"
    )
    assert closeout["closeout_scope"] == "SUMMARY_ONLY_NO_EXECUTION_OR_PROMOTION"
    assert closeout["prepared"] is True


def test_computational_physics_integration_closeout_acceptance_criteria() -> None:
    closeout = _json(CLOSEOUT_PATH)
    for key, value in closeout["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"


def test_computational_physics_integration_closeout_stack_layers_and_reviews() -> None:
    closeout = _json(CLOSEOUT_PATH)
    assert closeout["summary"]["stack_layer_count"] == 8
    assert closeout["summary"]["result_review_count"] == 8
    assert closeout["all_result_reviews_accepted"] is True
    assert len(closeout["stack_layers"]) == 8
    expected_layer_ids = [
        "capability_audit",
        "vvuq_ledger",
        "numerical_method_registry",
        "regime_recovery_matrix",
        "sensitivity_robustness_protocol",
        "referent_registry",
        "simulation_model_card_template",
        "prediction_and_falsifier_registry",
    ]
    assert [row["layer_id"] for row in closeout["stack_layers"]] == expected_layer_ids
    for row in closeout["stack_layers"]:
        assert row["result_review_accepted"] is True
        assert row["artifact_path"].startswith("formal/docs/release/")
        assert row["result_review_path"].startswith("formal/docs/release/")
        assert row["function"]


def test_computational_physics_integration_closeout_preserves_eight_row_lineage() -> None:
    closeout = _json(CLOSEOUT_PATH)
    assert closeout["row_count"] == 8
    assert closeout["expected_row_ids"] == EXPECTED_ROWS
    assert closeout["lineage_preserved"] is True
    for key, ids in closeout["lineage_row_ids"].items():
        assert ids == EXPECTED_ROWS, f"Lineage drift in {key}"


def test_computational_physics_integration_closeout_no_execution_validation_or_promotion() -> None:
    closeout = _json(CLOSEOUT_PATH)
    assert closeout["promotion_allowed_count"] == 0
    assert closeout["validation_upgrade_count"] == 0
    assert closeout["execution_claim_count"] == 0
    assert closeout["completion_claim_count"] == 0
    assert closeout["scoring_policy"] == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0"
    final = closeout["final_non_execution_readout"]
    for key, value in final.items():
        assert value is True, f"Expected explicit non-execution confirmation: {key}"


def test_computational_physics_integration_closeout_forbidden_effects_false_and_no_claim_language() -> None:
    closeout = _json(CLOSEOUT_PATH)
    forbidden = closeout["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = (
        json.dumps(closeout, sort_keys=True)
        + "\n"
        + _read(REPORT_PATH)
        + "\n"
        + _read(ROADMAP_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined


def test_computational_physics_integration_closeout_is_deterministic() -> None:
    generated_1 = build_closeout(captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    generated_2 = build_closeout(captured_at_utc=DEFAULT_CAPTURED_AT_UTC)
    assert generated_1 == generated_2
    assert _json(CLOSEOUT_PATH) == generated_1


def test_computational_physics_integration_closeout_is_pinned_and_next_action_updated() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    physics_text = _read(PHYSICS_ROADMAP_PATH)
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ) in roadmap_text
    assert "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_STATUS_v0: CLOSED_BOUNDED_NONCLAIM" in roadmap_text
    assert (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_OUTCOME_v0: "
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_PREPARED_AS_NONCLAIM_CREDIBILITY_INFRASTRUCTURE_"
        "WITH_NO_EXECUTION_OR_PROMOTION"
    ) in roadmap_text

    for ref in (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0",
        "formal/docs/release/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0.json",
        "formal/docs/paper/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_REPORT_v0.md",
        "formal/python/tools/computational_physics_integration_closeout_report.py",
        "formal/python/tests/test_computational_physics_integration_closeout_gate.py",
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT",
    ):
        assert ref in roadmap_text
        assert ref in physics_text
