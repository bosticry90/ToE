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
    / "QMStatTargetStatEntropySemanticsTheoremGap.lean"
)
SOURCE_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMStatTheoremGapReentryResultReview.lean"
)
RESIDUAL_PACKAGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QM_STAT_TransportResidualPackage.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_BOUNDED_ATTACK_20260510_v0.json"
)

REPORT_ID = (
    "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_BOUNDED_ATTACK_20260510_v0"
)
SURFACE_ID = "qm_stat_target_stat_entropy_semantics_theorem_gap_bounded_attack_v0"
CONSUMED_TARGET = "prepare_qm_stat_target_stat_entropy_semantics_theorem_gap_bounded_attack"
CONSUMED_REVIEW_TARGET = "review_qm_stat_theorem_gap_reentry_result"
CONSUMED_REVIEW_TOKEN = "QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_CONSUMED"
RESULT_TOKEN = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_SUPPLIED_ONLY"
NEXT_TARGET = "review_qm_stat_target_stat_entropy_semantics_theorem_gap_result"
SELECTED_GAP = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_THEOREM_GAP_v0"
SELECTED_OBLIGATION = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_OBLIGATION_v0"
RETAINED_BLOCKER = (
    "PHASE1-BLOCKER-QMSTAT-TARGET-STAT-ENTROPY-SEMANTICS-SUPPLIED-ONLY-RETAINED"
)
FRESH_DELTA_ID = "QM_STAT_TARGET_STAT_ENTROPY_SEMANTICS_SUPPLIED_ONLY_FRESH_DELTA_v0"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_qm_stat_target_stat_entropy_semantics_surface_records_supplied_only_attack() -> None:
    text = _read(SURFACE_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_REVIEW_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        SELECTED_GAP,
        SELECTED_OBLIGATION,
        RETAINED_BLOCKER,
        FRESH_DELTA_ID,
        "QMStatTargetSTATEntropySemanticPackage",
        "QMStatTargetSTATEntropySemanticData",
        "supplied_target_stat_entropy_semantics_constructs_package_v0",
        "target_stat_entropy_structure_supplies_semantics_v0",
        "finite_residual_package_does_not_force_target_stat_entropy_semantics_v0",
        "qm_stat_target_stat_entropy_semantics_consumes_live_target_v0",
        "qm_stat_target_stat_entropy_semantics_consumes_review_token_v0",
        "qm_stat_target_stat_entropy_semantics_selected_gap_id_v0",
        "qm_stat_target_stat_entropy_semantics_selected_obligation_v0",
        "qm_stat_target_stat_entropy_semantics_supplied_route_available_v0",
        "qm_stat_target_stat_entropy_semantics_residual_package_only_refuted_v0",
        "qm_stat_target_stat_entropy_semantics_selected_result_v0",
        "qm_stat_target_stat_entropy_semantics_result_token_v0",
        "qm_stat_target_stat_entropy_semantics_selected_next_target_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.QMStatTargetStatEntropySemanticsTheoremGap"
        in aggregate_text
    )


def test_qm_stat_target_stat_entropy_semantics_preserves_nonclaim_boundaries() -> None:
    text = _read(SURFACE_PATH)

    for token in {
        "qm_stat_target_stat_entropy_semantics_frontier_target_v0",
        "qm_stat_target_stat_entropy_semantics_not_lean_backed_v0",
        "qm_stat_target_stat_entropy_semantics_supplied_only_v0",
        "qm_stat_target_stat_entropy_semantics_not_still_blocked_v0",
        "qm_stat_target_stat_entropy_semantics_no_gap_discharge_v0",
        "qm_stat_target_stat_entropy_semantics_no_full_statistical_closure_v0",
        "qm_stat_target_stat_entropy_semantics_no_qm_stat_completion_v0",
        "qm_stat_target_stat_entropy_semantics_no_born_rule_recovery_v0",
        "qm_stat_target_stat_entropy_semantics_no_measurement_resolution_v0",
        "qm_stat_target_stat_entropy_semantics_no_seam_closure_v0",
        "qm_stat_target_stat_entropy_semantics_no_phase2_readiness_v0",
        "qm_stat_target_stat_entropy_semantics_no_empirical_adequacy_v0",
        "qm_stat_target_stat_entropy_semantics_no_canonical_toe_claim_v0",
        "qm_stat_target_stat_entropy_semantics_master_action_not_promoted_v0",
        "qm_stat_target_stat_entropy_semantics_qft_gr_not_authorized_v0",
        "qm_stat_target_stat_entropy_semantics_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_qm_stat_target_stat_entropy_semantics_report_records_supplied_only_result() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_result_review_target"] == CONSUMED_REVIEW_TARGET
    assert report["consumed_result_review_token"] == CONSUMED_REVIEW_TOKEN
    assert report["source_surface"] == _rel(SOURCE_REVIEW_PATH)
    assert report["surface"] == _rel(SURFACE_PATH)
    assert report["selected_gap"] == SELECTED_GAP
    assert report["selected_obligation"] == SELECTED_OBLIGATION
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["result_token"] == RESULT_TOKEN
    assert report["result_classification"] == "supplied_only"
    assert report["retained_blocker"] == RETAINED_BLOCKER
    assert report["fresh_delta_id"] == FRESH_DELTA_ID
    assert report["fresh_delta_kind"] == "supplied_only_classification"
    assert report["supplied_route"]["supplied_object"] == (
        "QMStatTargetSTATEntropySemanticPackage"
    )
    assert report["supplied_route"]["constructor"] == (
        "supplied_target_stat_entropy_semantics_constructs_package_v0"
    )
    assert report["refutation"]["lean_theorem"] == (
        "finite_residual_package_does_not_force_target_stat_entropy_semantics_v0"
    )
    assert report["attack_scope"] == {
        "addresses_selected_gap_only": True,
        "selected_gap_count": 1,
        "bounded_question": (
            "Can target STAT entropy semantics be derived from existing finite "
            "QM-STAT residual/package structures, or must the target semantics "
            "remain supplied/spec-backed?"
        ),
        "attack_executes_bounded_question": True,
    }
    assert report["result_matrix"] == {
        "target_stat_entropy_semantics_lean_backed": False,
        "target_stat_entropy_semantics_supplied_only": True,
        "target_stat_entropy_semantics_still_blocked": False,
        "theorem_gap_discharged": False,
    }


def test_qm_stat_target_stat_entropy_semantics_report_preserves_nonclaims() -> None:
    report = _json(REPORT_PATH)

    assert not any(report["nonclaim_boundaries"].values())
    assert report["next_action"] == NEXT_TARGET
    assert report["source_report"] == (
        "formal/docs/release/QM_STAT_THEOREM_GAP_REENTRY_RESULT_REVIEW_20260510_v0.json"
    )
    assert "import ToeFormal.Bridges.QM_STAT_TransportResidualPackage" in _read(
        SURFACE_PATH
    )


def test_qm_stat_target_stat_entropy_semantics_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_qm_stat_target_stat_entropy_semantics_theorem_gap_gate.py"
    )
