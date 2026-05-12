from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatEntropySemanticsSupportingAssumptionMap.lean"
)
SOURCE_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterQMStatEntropySemanticsGap.lean"
)
SOURCE_ATTACK_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTargetStatEntropySemanticsTheoremGap.lean"
)
SOURCE_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTargetStatEntropySemanticsTheoremGapResultReview.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_20260510_v0.json"
)
SOURCE_SELECTOR_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP_20260510_v0.json"
)
SOURCE_ATTACK_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_BOUNDED_ATTACK_20260510_v0.json"
)
SOURCE_REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_20260510_v0.json"
)

REPORT_ID = "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_20260510_v0"
SURFACE_ID = "qm_stat_entropy_semantics_supporting_assumption_map_v0"
CONSUMED_TARGET = "prepare_qm_stat_entropy_semantics_supporting_assumption_map"
CONSUMED_SELECTOR_TOKEN = (
    "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_QM_STAT_ENTROPY_SEMANTICS_GAP"
)
RESULT_TOKEN = "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP_PREPARED"
NEXT_TARGET = "review_qm_stat_entropy_semantics_supporting_assumption_map_result"
SELECTED_LANE = "QM_STAT_ENTROPY_SEMANTICS_SUPPORTING_ASSUMPTION_MAP"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
SUPPLIED_ONLY_RESULT_TOKEN = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_SUPPLIED_ONLY"
SUPPLIED_ONLY_REVIEW_TOKEN = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_RESULT_REVIEW_CONSUMED_SUPPLIED_ONLY"
)
ALLOWED_AUTHORITY_CLASSIFICATIONS = [
    "Lean-backed",
    "spec-backed",
    "supplied-only",
    "blocked",
    "not yet represented",
]
EXPECTED_ASSUMPTION_AUTHORITY = {
    "target_entropy_functional_definition_required": "Lean-backed",
    "statistical_state_domain_semantics_required": "supplied-only",
    "normalization_or_probability_mass_condition_required": "not yet represented",
    "finite_support_or_summability_condition_required": "Lean-backed",
    "log_domain_zero_handling_convention_required": "not yet represented",
    "transport_alignment_relation_required": "Lean-backed",
    "residual_zero_bridge_condition_required": "Lean-backed",
    "comparison_target_semantics_required": "supplied-only",
}
EXPECTED_LABELS = {
    "target entropy functional definition required",
    "statistical state/domain semantics required",
    "normalization or probability-mass condition required",
    "finite-support or summability condition required",
    "log-domain / zero-handling convention required",
    "transport/alignment relation required",
    "residual-zero bridge condition required",
    "comparison target semantics required",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_qm_stat_entropy_semantics_supporting_assumption_map_surface_records_core_map() -> None:
    text = _read(SURFACE_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_SELECTOR_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        SELECTED_LANE,
        SELECTED_GAP,
        "QMStatEntropySemanticsAssumptionAuthority",
        "QMStatEntropySemanticsSupportingAssumptionClass",
        "QMStatEntropySemanticsSupportingAssumptionRow",
        "QMStatEntropySemanticsSupportingAssumptionMapStatus",
        "qmStatEntropySemanticsSupportingAssumptionRowsV0",
        "qm_stat_entropy_semantics_supporting_assumption_map_consumes_live_target_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_consumes_selector_token_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_result_token_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_next_target_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_selected_lane_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_selected_gap_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_row_count_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_authority_class_count_v0",
    } | set(EXPECTED_ASSUMPTION_AUTHORITY) | EXPECTED_LABELS:
        assert token in text

    assert (
        "import ToeFormal.Derivation.QMStatEntropySemanticsSupportingAssumptionMap"
        in aggregate_text
    )


def test_qm_stat_entropy_semantics_supporting_assumption_map_surface_records_authority_classes() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        "target_entropy_functional_definition_authority_v0",
        "statistical_state_domain_semantics_authority_v0",
        "normalization_or_probability_mass_condition_authority_v0",
        "finite_support_or_summability_condition_authority_v0",
        "log_domain_zero_handling_convention_authority_v0",
        "transport_alignment_relation_authority_v0",
        "residual_zero_bridge_condition_authority_v0",
        "comparison_target_semantics_authority_v0",
    } | set(ALLOWED_AUTHORITY_CLASSIFICATIONS):
        assert token in text


def test_qm_stat_entropy_semantics_supporting_assumption_map_surface_preserves_nonclaims() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        "qm_stat_entropy_semantics_supporting_assumption_map_supplied_only_preserved_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_does_not_attempt_discharge_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_no_lean_backed_discharge_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_no_gap_closure_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_no_qm_stat_completion_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_no_seam_closure_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_no_phase2_readiness_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_no_empirical_adequacy_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_no_canonical_toe_claim_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_master_action_not_promoted_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_qft_gr_not_authorized_v0",
        "qm_stat_entropy_semantics_supporting_assumption_map_manifest_not_enrolled_v0",
        "map_attempts_theorem_discharge := False",
    }:
        assert token in text


def test_qm_stat_entropy_semantics_supporting_assumption_map_report_records_rows() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["map_status"] == "prepared_assumption_map_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_SELECTOR_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["selected_lane"] == SELECTED_LANE
    assert report["assumption_map_surface"] == _rel(SURFACE_PATH)
    assert report["source_selector_surface"] == _rel(SOURCE_SELECTOR_PATH)
    assert report["source_selector_report"] == _rel(SOURCE_SELECTOR_REPORT_PATH)
    assert report["source_supplied_only_attack_surface"] == _rel(SOURCE_ATTACK_PATH)
    assert report["source_supplied_only_attack_report"] == _rel(SOURCE_ATTACK_REPORT_PATH)
    assert report["source_supplied_only_review_surface"] == _rel(SOURCE_REVIEW_PATH)
    assert report["source_supplied_only_review_report"] == _rel(SOURCE_REVIEW_REPORT_PATH)
    assert report["focused_gate"] == (
        "formal/python/tests/test_qm_stat_entropy_semantics_supporting_assumption_map_gate.py"
    )
    assert report["authorized_effect"] == "PREPARE_SUPPORTING_ASSUMPTION_MAP_ONLY"
    assert report["map_attempts_theorem_discharge"] is False
    assert report["allowed_authority_classifications"] == ALLOWED_AUTHORITY_CLASSIFICATIONS

    rows = report["assumption_classes"]
    assert len(rows) == 8
    assert {row["class_id"] for row in rows} == set(EXPECTED_ASSUMPTION_AUTHORITY)
    assert {row["label"] for row in rows} == EXPECTED_LABELS
    assert {
        row["class_id"]: row["authority_classification"] for row in rows
    } == EXPECTED_ASSUMPTION_AUTHORITY
    assert all(row["closure_requirement"] for row in rows)
    assert all(row["existing_surface"] for row in rows)


def test_qm_stat_entropy_semantics_supporting_assumption_map_report_preserves_supplied_only_basis() -> None:
    report = _json(REPORT_PATH)

    assert report["selected_gap_basis"] == {
        "selected_gap": SELECTED_GAP,
        "selected_obligation": SELECTED_OBLIGATION,
        "source_result_token": SUPPLIED_ONLY_RESULT_TOKEN,
        "source_review_token": SUPPLIED_ONLY_REVIEW_TOKEN,
        "target_stat_entropy_semantics_authority": (
            "SUPPLIED_ONLY_TARGET_STAT_ENTROPY_SEMANTICS_RETAINED"
        ),
        "lean_backed_entropy_semantics_discharge": False,
        "theorem_gap_discharged": False,
    }
    assert report["authority_summary"] == {
        "Lean-backed": 4,
        "spec-backed": 0,
        "supplied-only": 2,
        "blocked": 0,
        "not yet represented": 2,
    }
    assert report["nonclaim_boundaries"] == {
        "map_attempts_theorem_discharge": False,
        "target_stat_entropy_semantics_lean_backed": False,
        "target_stat_entropy_semantics_supplied_only": True,
        "theorem_gap_discharged": False,
        "qm_stat_pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "master_action_promotion_authorized": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_action_after_assumption_map"] == NEXT_TARGET
    assert (
        "maps the supporting assumptions required for the supplied-only QM-STAT target entropy semantics gap"
        in report["acceptance_condition"]
    )


def test_qm_stat_entropy_semantics_supporting_assumption_map_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_entropy_semantics_supporting_assumption_map_gate.py"
    )
