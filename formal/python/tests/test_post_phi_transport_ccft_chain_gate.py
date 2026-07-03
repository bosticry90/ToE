from __future__ import annotations

import json
import importlib
from pathlib import Path
from typing import Any

import pytest

from formal.python.tests.strict_physics_state_helpers import (
    README_PATH,
    ROADMAP_PATH,
    STATE_PATH,
    STRICT_MAP_PATH,
    CURRENT_AUTHORITATIVE_SURFACES_PATH,
    REPO_ROOT,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    loop_registry,
    read_text,
    workstream,
)
from formal.python.tools.post_phi_transport_ccft_chain_reports import (
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_STATUS_WORDING,
    LEAN_STATUS_WORDING_LINES,
    LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL,
    LOCAL_PHI_TRIAD_EQUATIONS,
    ORDERED_STAGE_KEYS,
    SCOPED_LEAN_TARGETS_STATUS,
    STAGES,
    build_stage_payload,
    lean_path,
    release_path,
)


FINAL_LIVE_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_observable_definition_semantics_packet"
)
FINAL_PREVIOUS_TARGET = (
    "review_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result"
)
BASELINE_SEMANTICS_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet"
)
TOLERANCE_REGISTRY_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_tolerance_registry_packet_result"
)
TOLERANCE_REGISTRY_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_tolerance_registry_packet"
)
SELECTED_CANDIDATE_REVIEW_TARGET = (
    "review_selected_ccft_empirical_discriminator_candidate_packet_result"
)
SELECTED_CANDIDATE_PACKET_TARGET = (
    "prepare_selected_ccft_empirical_discriminator_candidate_packet"
)
PRIORITY_PACKET_TARGET = (
    "prepare_ccft_empirical_discriminator_candidate_priority_selection_packet"
)
PRIORITY_REVIEW_TARGET = (
    "review_ccft_empirical_discriminator_candidate_priority_selection_packet_result"
)
EMPIRICAL_PACKET_TARGET = "prepare_ccft_empirical_discriminator_candidate_map_packet"
EMPIRICAL_REVIEW_TARGET = "review_ccft_empirical_discriminator_candidate_map_packet_result"
VARIATIONAL_PACKET_TARGET = "prepare_ccft_full_variational_action_program_packet"
VARIATIONAL_REVIEW_TARGET = "review_ccft_full_variational_action_program_packet_result"
FINAL_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SelectedCCFTEmpiricalDiscriminatorBaselineComparisonSemanticsPacketResultReview.lean"
)
FINAL_REPORT = (
    "formal/docs/release/"
    "SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_"
    "SEMANTICS_PACKET_RESULT_REVIEW_20260702_v0.json"
)
FINAL_OUTCOME = STAGES["baseline_semantics_review"].outcome_id
FINAL_STRICT_OUTCOME = STAGES["baseline_semantics_review"].strict_outcome_id
FINAL_KIND = (
    "selected_ccft_empirical_discriminator_observable_definition_semantics_packet"
)
NEXT_PACKET_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_PREPARED_LAGRANGIAN_"
    "HAMILTONIAN_SOURCE_AND_TRANSPORT_TARGETS_NO_ACTION_EMBEDDING_OR_"
    "MASTER_ACTION_PROMOTION"
)
NEXT_PACKET_STRICT_OUTCOME = (
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_PREPARED_AS_REQUIRED_PRE_"
    "DERIVATION_PLAN_NO_CK_VARIATION_OR_CCFT_VALIDATION"
)
LOCAL_PHI_TRIAD_REGISTRY_TEXT = "; ".join(LOCAL_PHI_TRIAD_EQUATIONS)

PUBLIC_SURFACES = (
    README_PATH,
    STATE_PATH,
    ROADMAP_PATH,
    STRICT_MAP_PATH,
    CURRENT_AUTHORITATIVE_SURFACES_PATH,
)

WRAPPER_BY_STAGE = {
    "selector": (
        "formal/python/tools/"
        "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_report.py"
    ),
    "selector_review": (
        "formal/python/tools/"
        "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_result_review_report.py"
    ),
    "triad_packet": (
        "formal/python/tools/"
        "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "packet_report.py"
    ),
    "triad_review": (
        "formal/python/tools/"
        "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "result_review_report.py"
    ),
    "roadmap_packet": (
        "formal/python/tools/coherence_admissibility_bridge_roadmap_rebase_"
        "packet_report.py"
    ),
    "roadmap_review": (
        "formal/python/tools/coherence_admissibility_bridge_roadmap_rebase_"
        "result_review_report.py"
    ),
    "crosswalk_packet": (
        "formal/python/tools/ccft_to_toe_object_crosswalk_packet_report.py"
    ),
    "ck_index_packet": (
        "formal/python/tools/ccft_ck_admissibility_obligation_index_packet_report.py"
    ),
    "ck_index_review": (
        "formal/python/tools/"
        "ccft_ck_admissibility_obligation_index_packet_result_review_report.py"
    ),
    "variational_packet": (
        "formal/python/tools/ccft_full_variational_action_program_packet_report.py"
    ),
    "variational_review": (
        "formal/python/tools/"
        "ccft_full_variational_action_program_packet_result_review_report.py"
    ),
    "empirical_packet": (
        "formal/python/tools/"
        "ccft_empirical_discriminator_candidate_map_packet_report.py"
    ),
    "empirical_review": (
        "formal/python/tools/"
        "ccft_empirical_discriminator_candidate_map_packet_result_review_report.py"
    ),
    "priority_packet": (
        "formal/python/tools/"
        "ccft_empirical_discriminator_candidate_priority_selection_packet_report.py"
    ),
    "priority_review": (
        "formal/python/tools/"
        "ccft_empirical_discriminator_candidate_priority_selection_packet_result_review_report.py"
    ),
    "selected_candidate_packet": (
        "formal/python/tools/selected_ccft_empirical_discriminator_candidate_packet_report.py"
    ),
    "selected_candidate_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_candidate_packet_result_review_report.py"
    ),
    "tolerance_registry_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_report.py"
    ),
    "tolerance_registry_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review_report.py"
    ),
    "baseline_semantics_packet": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_report.py"
    ),
    "baseline_semantics_review": (
        "formal/python/tools/"
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review_report.py"
    ),
}

WRAPPER_BUILD_FUNCTION_BY_STAGE = {
    "selector": (
        "formal.python.tools."
        "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_report",
        "build_ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout",
    ),
    "selector_review": (
        "formal.python.tools."
        "ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_result_review_report",
        "build_ck_family_theorem_linkage_obligation_selection_after_phi_transport_"
        "closeout_result_review",
    ),
    "triad_packet": (
        "formal.python.tools."
        "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "packet_report",
        "build_phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "packet",
    ),
    "triad_review": (
        "formal.python.tools."
        "phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "result_review_report",
        "build_phi_ck_source_bridge_transport_theorem_linkage_family_synthesis_"
        "result_review",
    ),
    "roadmap_packet": (
        "formal.python.tools.coherence_admissibility_bridge_roadmap_rebase_"
        "packet_report",
        "build_coherence_admissibility_bridge_roadmap_rebase_packet",
    ),
    "roadmap_review": (
        "formal.python.tools.coherence_admissibility_bridge_roadmap_rebase_"
        "result_review_report",
        "build_coherence_admissibility_bridge_roadmap_rebase_result_review",
    ),
    "crosswalk_packet": (
        "formal.python.tools.ccft_to_toe_object_crosswalk_packet_report",
        "build_ccft_to_toe_object_crosswalk_packet",
    ),
    "ck_index_packet": (
        "formal.python.tools.ccft_ck_admissibility_obligation_index_packet_report",
        "build_ccft_ck_admissibility_obligation_index_packet",
    ),
    "ck_index_review": (
        "formal.python.tools."
        "ccft_ck_admissibility_obligation_index_packet_result_review_report",
        "build_ccft_ck_admissibility_obligation_index_packet_result_review",
    ),
    "variational_packet": (
        "formal.python.tools.ccft_full_variational_action_program_packet_report",
        "build_ccft_full_variational_action_program_packet",
    ),
    "variational_review": (
        "formal.python.tools."
        "ccft_full_variational_action_program_packet_result_review_report",
        "build_ccft_full_variational_action_program_packet_result_review",
    ),
    "empirical_packet": (
        "formal.python.tools.ccft_empirical_discriminator_candidate_map_packet_report",
        "build_ccft_empirical_discriminator_candidate_map_packet",
    ),
    "empirical_review": (
        "formal.python.tools."
        "ccft_empirical_discriminator_candidate_map_packet_result_review_report",
        "build_ccft_empirical_discriminator_candidate_map_packet_result_review",
    ),
    "priority_packet": (
        "formal.python.tools."
        "ccft_empirical_discriminator_candidate_priority_selection_packet_report",
        "build_ccft_empirical_discriminator_candidate_priority_selection_packet",
    ),
    "priority_review": (
        "formal.python.tools."
        "ccft_empirical_discriminator_candidate_priority_selection_packet_result_review_report",
        "build_ccft_empirical_discriminator_candidate_priority_selection_packet_result_review",
    ),
    "selected_candidate_packet": (
        "formal.python.tools.selected_ccft_empirical_discriminator_candidate_packet_report",
        "build_selected_ccft_empirical_discriminator_candidate_packet",
    ),
    "selected_candidate_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_candidate_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_candidate_packet_result_review",
    ),
    "tolerance_registry_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_report",
        "build_selected_ccft_empirical_discriminator_tolerance_registry_packet",
    ),
    "tolerance_registry_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review",
    ),
    "baseline_semantics_packet": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_report",
        "build_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet",
    ),
    "baseline_semantics_review": (
        "formal.python.tools."
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review_report",
        "build_selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review",
    ),
}

PAPER_DOCS = (
    "formal/docs/paper/TOE_COHERENCE_ADMISSIBILITY_BRIDGE_HYPOTHESIS_v0.md",
    "formal/docs/paper/TOE_COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_v1.md",
    "formal/docs/paper/CCFT_TO_TOE_OBJECT_CROSSWALK_v0.md",
    "formal/docs/paper/CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0.md",
    "formal/docs/paper/CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0.md",
    "formal/docs/paper/CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0.md",
    "formal/docs/paper/CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_v0.md",
    "formal/docs/paper/CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PRIORITY_SELECTION_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_TOLERANCE_REGISTRY_PACKET_RESULT_REVIEW_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_v0.md",
    "formal/docs/paper/SELECTED_CCFT_EMPIRICAL_DISCRIMINATOR_BASELINE_COMPARISON_SEMANTICS_PACKET_RESULT_REVIEW_v0.md",
)

JSON_FALSE_FLAGS = (
    "proof_execution_authorized",
    "proof_attempt_executed",
    "theorem_discharged",
    "new_theorem_discharge",
    "theorem_linkage_obligation_discharged",
    "gap_discharged",
    "any_gap_discharged",
    "any_gap_closed",
    "phi_sector_closure_claimed",
    "full_scalar_qft_closure_claimed",
    "full_scalar_QFT_closure_claimed",
    "qft_gr_closure_claimed",
    "em_qft_closure_claimed",
    "gr_qm_closure_claimed",
    "sr_cosmo_closure_claimed",
    "qm_stat_closure_claimed",
    "pillar_closure_claim",
    "seam_closure_claim",
    "general_C_k_closure",
    "general_C_k_theorem_linkage_closure",
    "C_k_rule_promoted",
    "rule_promoted",
    "C_k_action_embedding_claimed",
    "C_k_action_variation_executed",
    "action_embedding_claimed",
    "action_variation_executed",
    "empirical_prediction_claimed",
    "empirical_validation_claimed",
    "CCFT_validated",
    "CCFT_fundamental_physics_claimed",
    "CCFT_derivation_from_master_action_claimed",
    "master_action_promoted",
    "master_action_promotion_authorized",
    "historical_20260619_rule_family_artifacts_overwritten",
    "new_triad_called_rule_family_closeout",
    "full_toeformal_aggregate_passed",
    "full_toeformal_aggregate_failed",
    "full_toeformal_aggregate_timed_out",
)


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(read_text(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _assert_registry_nonclaims(row: dict[str, Any]) -> None:
    for flag in JSON_FALSE_FLAGS:
        assert row[flag] == "no", flag


@pytest.mark.parametrize("stage_key", ORDERED_STAGE_KEYS)
def test_post_phi_transport_ccft_json_reports_match_builders(stage_key: str) -> None:
    spec = STAGES[stage_key]
    module_name, build_function_name = WRAPPER_BUILD_FUNCTION_BY_STAGE[stage_key]
    wrapper_builder = getattr(importlib.import_module(module_name), build_function_name)
    assert release_path(spec).exists()
    assert lean_path(spec).exists()
    assert (REPO_ROOT / WRAPPER_BY_STAGE[stage_key]).exists()
    assert wrapper_builder() == build_stage_payload(stage_key)
    assert _read_json(release_path(spec)) == wrapper_builder()


def test_post_phi_transport_ccft_chain_order_and_report_boundaries() -> None:
    previous_spec = None
    for stage_key in ORDERED_STAGE_KEYS:
        spec = STAGES[stage_key]
        report = _read_json(release_path(spec))
        if previous_spec is not None:
            assert previous_spec.selected_next_target == spec.consumed_target
            assert previous_spec.selected_next_target_kind == spec.consumed_target_kind
        previous_spec = spec

        assert report["lean_status_wording"] == LEAN_STATUS_WORDING
        assert report["lean_status_wording_lines"] == LEAN_STATUS_WORDING_LINES
        assert (
            report["full_toeformal_aggregate_status"]
            == FULL_TOEFORMAL_AGGREGATE_STATUS
        )
        assert report["scoped_lean_targets_status"] == SCOPED_LEAN_TARGETS_STATUS
        assert report["local_phi_triad_label"] == (
            LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL
        )
        assert report["local_phi_theorem_linkage_triad"] == LOCAL_PHI_TRIAD_EQUATIONS
        empirical_map_prepared = stage_key in {
            "empirical_packet",
            "empirical_review",
            "priority_packet",
            "priority_review",
            "selected_candidate_packet",
            "selected_candidate_review",
            "tolerance_registry_packet",
            "tolerance_registry_review",
            "baseline_semantics_packet",
            "baseline_semantics_review",
        }
        assert (
            report["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
            is empirical_map_prepared
        )
        assert report["later_ccft_artifacts_fully_populated"] is empirical_map_prepared
        for flag in JSON_FALSE_FLAGS:
            assert report[flag] is False, flag

    assert STAGES["selector"].consumed_target == (
        "select_next_ck_family_theorem_linkage_obligation_after_phi_transport_"
        "closeout"
    )
    assert STAGES["ck_index_packet"].selected_next_target == (
        "review_ccft_ck_admissibility_obligation_index_packet_result"
    )
    assert STAGES["ck_index_review"].selected_next_target == (
        VARIATIONAL_PACKET_TARGET
    )
    assert STAGES["variational_packet"].selected_next_target == VARIATIONAL_REVIEW_TARGET
    assert STAGES["variational_review"].selected_next_target == EMPIRICAL_PACKET_TARGET
    assert STAGES["empirical_packet"].selected_next_target == EMPIRICAL_REVIEW_TARGET
    assert STAGES["empirical_review"].selected_next_target == PRIORITY_PACKET_TARGET
    assert STAGES["priority_packet"].selected_next_target == PRIORITY_REVIEW_TARGET
    assert (
        STAGES["priority_review"].selected_next_target
        == SELECTED_CANDIDATE_PACKET_TARGET
    )
    assert (
        STAGES["selected_candidate_packet"].selected_next_target
        == SELECTED_CANDIDATE_REVIEW_TARGET
    )
    assert (
        STAGES["selected_candidate_review"].selected_next_target
        == TOLERANCE_REGISTRY_PACKET_TARGET
    )
    assert (
        STAGES["tolerance_registry_packet"].selected_next_target
        == TOLERANCE_REGISTRY_REVIEW_TARGET
    )
    assert (
        STAGES["tolerance_registry_review"].selected_next_target
        == BASELINE_SEMANTICS_PACKET_TARGET
    )
    assert STAGES["baseline_semantics_packet"].selected_next_target == FINAL_PREVIOUS_TARGET
    assert STAGES["baseline_semantics_review"].selected_next_target == FINAL_LIVE_TARGET


def test_local_phi_triad_and_ccft_roadmap_staging_boundaries() -> None:
    for stage_key in ("triad_packet", "triad_review"):
        report = _read_json(release_path(STAGES[stage_key]))
        assert report["local_phi_theorem_linkage_triad"] == [
            "C_source^phi = 0",
            "C_bridge^phi = 0",
            "C_transport^phi = 0",
        ]
        assert report["local_phi_theorem_linkage_triad_count"] == 3
        assert "not a phi C_k rule-family closeout" in report["triad_boundary"]
        assert report["historical_20260619_rule_family_artifacts_overwritten"] is False
        assert report["new_triad_called_rule_family_closeout"] is False

    for stage_key in ("roadmap_packet", "roadmap_review"):
        report = _read_json(release_path(STAGES[stage_key]))
        assert report["roadmap_rebase_lists_follow_on_artifacts_only"] is True
        assert report["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is False
        assert report["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is False
        assert report["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is False
        assert (
            report["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
            is False
        )
        assert report["ccft_role"] == "candidate mesoscopic coherence bridge layer"
        assert report["master_action_role"] == (
            "non-promoted candidate organizing surface"
        )
        assert report["C_k_role"] == "admissibility-only bridge-checking family"
        assert report["phi_triad_role"] == "local theorem-linkage family only"

    crosswalk = _read_json(release_path(STAGES["crosswalk_packet"]))
    assert crosswalk["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert crosswalk["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is False
    assert crosswalk["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is False
    assert (
        crosswalk["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
        is False
    )

    ck_index = _read_json(release_path(STAGES["ck_index_packet"]))
    assert ck_index["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert ck_index["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is True
    assert ck_index["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is False
    assert (
        ck_index["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
        is False
    )

    variational = _read_json(release_path(STAGES["variational_packet"]))
    assert variational["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert variational["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is True
    assert variational["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is True
    assert (
        variational["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"]
        is False
    )
    assert variational["ccft_full_variational_action_program_target_count"] == 13
    for target in (
        "CCFT full Lagrangian candidate targets",
        "CCFT full Hamiltonian candidate targets",
        "phi-sector variational route targets",
        "chi-sector variational route targets",
        "R/K rotor-curvature variational route targets",
        "CCFT stress-energy/source candidate targets",
        "CCFT C_source derivation targets",
        "CCFT C_bridge derivation targets",
        "CCFT C_transport component-derivation targets",
        "CCFT C_exchange phi-chi exchange-balance targets",
        "required blockers before action embedding",
        "required blockers before C_k variation",
        "required blockers before empirical discriminator claims",
    ):
        assert target in variational["ccft_full_variational_action_program_targets"]
    assert variational["C_k_action_embedding_authorized"] is False
    assert variational["C_k_variation_authorized"] is False
    assert variational["empirical_discriminator_claims_authorized"] is False

    empirical = _read_json(release_path(STAGES["empirical_packet"]))
    assert empirical["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert empirical["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is True
    assert empirical["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is True
    assert empirical["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] is True
    assert empirical["later_ccft_artifacts_fully_populated"] is True
    assert empirical["ccft_empirical_discriminator_candidate_map_target_count"] == 11
    for target in (
        "candidate measurable systems",
        "candidate observables",
        "candidate control variables",
        "candidate baseline models",
        "candidate failure modes",
        "candidate falsifiers",
        "candidate numerical-vs-physical comparison routes",
        "candidate empirical-discriminator questions",
        "required blockers before empirical claim",
        "required blockers before CCFT validation",
        "required blockers before pillar or seam relevance",
    ):
        assert target in empirical["ccft_empirical_discriminator_candidate_map_targets"]
    assert empirical["empirical_claim_authorized"] is False
    assert empirical["pillar_closure_authorized"] is False

    priority = _read_json(release_path(STAGES["priority_packet"]))
    assert priority["CCFT_TO_TOE_OBJECT_CROSSWALK_v0_prepared"] is True
    assert priority["CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0_prepared"] is True
    assert priority["CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0_prepared"] is True
    assert priority["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] is True
    assert priority["later_ccft_artifacts_fully_populated"] is True
    assert (
        priority[
            "ccft_empirical_discriminator_candidate_priority_selection_action_count"
        ]
        == 10
    )
    assert (
        priority[
            "ccft_empirical_discriminator_candidate_priority_selection_criteria_count"
        ]
        == 7
    )
    assert priority["selected_top_candidate_for_future_packet_only"] == (
        "controlled_mesoscopic_coherence_platform_candidate"
    )
    assert priority["future_packet_preparation_only"] is True
    assert priority["empirical_test_executed"] is False
    assert priority["CCFT_validated"] is False


def test_post_phi_transport_ccft_registry_rotation_and_stage_rows() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    payload = loop_registry()
    state = payload["current_target_state"]
    assert state["previous_live_next_target"] == FINAL_PREVIOUS_TARGET
    assert state["live_next_target"] == FINAL_LIVE_TARGET
    assert state["active_lane"] == FINAL_LIVE_TARGET
    assert state["live_next_target_evidence"] == FINAL_EVIDENCE
    assert state["live_next_target_report"] == FINAL_REPORT
    assert state["live_next_target_outcome"] == FINAL_OUTCOME
    assert state["live_next_target_strict_outcome"] == FINAL_STRICT_OUTCOME
    assert state["live_next_target_kind"] == FINAL_KIND
    assert payload["CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0"] == FINAL_STRICT_OUTCOME
    assert payload["CURRENT_LIVE_TARGET_KIND_v0"] == FINAL_KIND

    for stage_key in ORDERED_STAGE_KEYS:
        spec = STAGES[stage_key]
        row = workstream(spec.consumed_target, payload)
        assert row["status"] == "paused"
        assert row["active_lane"] == spec.consumed_target
        assert row["authorized_next_strict_target"] == spec.consumed_target
        assert row["authorized_target"] == spec.consumed_target
        assert row["authorization_evidence"] == _rel(lean_path(spec))
        assert row["report"] == _rel(release_path(spec))
        assert row["packet_result"] == spec.outcome_id
        assert row["strict_packet_result"] == spec.strict_outcome_id
        assert row["selected_next_target"] == spec.selected_next_target
        assert row["selected_next_target_kind"] == spec.selected_next_target_kind
        assert row["local_phi_triad_label"] == (
            LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL
        )
        assert row["local_phi_theorem_linkage_triad"] == (
            LOCAL_PHI_TRIAD_REGISTRY_TEXT
        )
        empirical_map_prepared = (
            "yes"
            if stage_key
            in {
                "empirical_packet",
                "empirical_review",
                "priority_packet",
                "priority_review",
                "selected_candidate_packet",
                "selected_candidate_review",
                "tolerance_registry_packet",
                "tolerance_registry_review",
                "baseline_semantics_packet",
                "baseline_semantics_review",
            }
            else "no"
        )
        assert row["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] == (
            empirical_map_prepared
        )
        assert row["later_ccft_artifacts_fully_populated"] == empirical_map_prepared
        if spec.result_kind == "selection":
            assert row["selection_result"] == spec.outcome_id
            assert row["strict_selection_result"] == spec.strict_outcome_id
        if spec.result_kind == "review":
            assert row["review_result"] == spec.outcome_id
            assert row["strict_review_result"] == spec.strict_outcome_id
        _assert_registry_nonclaims(row)

    ck_review = workstream(
        "review_ccft_ck_admissibility_obligation_index_packet_result", payload
    )
    assert ck_review["status"] == "paused"
    assert ck_review["review_result"] == STAGES["ck_index_review"].outcome_id
    assert ck_review["strict_review_result"] == (
        STAGES["ck_index_review"].strict_outcome_id
    )
    assert ck_review["selected_next_target"] == VARIATIONAL_PACKET_TARGET
    assert ck_review["selected_next_target_kind"] == (
        "ccft_full_variational_action_program_packet"
    )
    assert ck_review["prepared_packet_result"] == STAGES["ck_index_packet"].outcome_id
    assert ck_review["prepared_packet_strict_result"] == (
        STAGES["ck_index_packet"].strict_outcome_id
    )
    _assert_registry_nonclaims(ck_review)

    prepared_packet = workstream(VARIATIONAL_PACKET_TARGET, payload)
    assert prepared_packet["status"] == "paused"
    assert prepared_packet["packet_result"] == STAGES["variational_packet"].outcome_id
    assert prepared_packet["strict_packet_result"] == (
        STAGES["variational_packet"].strict_outcome_id
    )
    assert prepared_packet["selected_next_target"] == VARIATIONAL_REVIEW_TARGET
    assert prepared_packet["selected_next_target_kind"] == (
        "ccft_full_variational_action_program_packet_result_review"
    )
    assert prepared_packet["ccft_full_variational_action_program_target_count"] == 13
    assert prepared_packet["C_k_action_embedding_authorized"] == "no"
    assert prepared_packet["C_k_variation_authorized"] == "no"
    assert prepared_packet["empirical_discriminator_claims_authorized"] == "no"
    _assert_registry_nonclaims(prepared_packet)

    variational_review = workstream(VARIATIONAL_REVIEW_TARGET, payload)
    assert variational_review["status"] == "paused"
    assert variational_review["review_result"] == STAGES["variational_review"].outcome_id
    assert variational_review["strict_review_result"] == (
        STAGES["variational_review"].strict_outcome_id
    )
    assert variational_review["prepared_packet_result"] == (
        STAGES["variational_packet"].outcome_id
    )
    assert variational_review["prepared_packet_strict_result"] == (
        STAGES["variational_packet"].strict_outcome_id
    )
    assert variational_review["selected_next_target"] == EMPIRICAL_PACKET_TARGET
    assert variational_review["selected_next_target_kind"] == (
        "ccft_empirical_discriminator_candidate_map_packet"
    )
    assert variational_review[
        "ccft_full_variational_action_program_review_acceptance_item_count"
    ] == 22
    assert "CCFT full Lagrangian candidate targets indexed" in variational_review[
        "ccft_full_variational_action_program_review_acceptance_items"
    ]
    assert variational_review["C_k_action_embedding_authorized"] == "no"
    assert variational_review["C_k_variation_authorized"] == "no"
    assert variational_review["empirical_discriminator_claims_authorized"] == "no"
    _assert_registry_nonclaims(variational_review)

    empirical_packet = workstream(EMPIRICAL_PACKET_TARGET, payload)
    assert empirical_packet["status"] == "paused"
    assert empirical_packet["packet_result"] == STAGES["empirical_packet"].outcome_id
    assert empirical_packet["strict_packet_result"] == (
        STAGES["empirical_packet"].strict_outcome_id
    )
    assert empirical_packet["selected_next_target"] == EMPIRICAL_REVIEW_TARGET
    assert empirical_packet["selected_next_target_kind"] == (
        "ccft_empirical_discriminator_candidate_map_packet_result_review"
    )
    assert (
        empirical_packet["ccft_empirical_discriminator_candidate_map_target_count"]
        == 11
    )
    assert "candidate measurable systems" in empirical_packet[
        "ccft_empirical_discriminator_candidate_map_targets"
    ]
    assert "candidate falsifiers" in empirical_packet[
        "ccft_empirical_discriminator_candidate_map_targets"
    ]
    assert empirical_packet["empirical_claim_authorized"] == "no"
    assert empirical_packet["pillar_closure_authorized"] == "no"
    assert empirical_packet["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] == "yes"
    assert empirical_packet["later_ccft_artifacts_fully_populated"] == "yes"
    _assert_registry_nonclaims(empirical_packet)

    empirical_review = workstream(EMPIRICAL_REVIEW_TARGET, payload)
    assert empirical_review["status"] == "paused"
    assert empirical_review["review_result"] == STAGES["empirical_review"].outcome_id
    assert empirical_review["strict_review_result"] == (
        STAGES["empirical_review"].strict_outcome_id
    )
    assert empirical_review["prepared_packet_result"] == (
        STAGES["empirical_packet"].outcome_id
    )
    assert empirical_review["prepared_packet_strict_result"] == (
        STAGES["empirical_packet"].strict_outcome_id
    )
    assert empirical_review["selected_next_target"] == PRIORITY_PACKET_TARGET
    assert empirical_review["selected_next_target_kind"] == (
        "ccft_empirical_discriminator_candidate_priority_selection_packet"
    )
    assert (
        empirical_review[
            "ccft_empirical_discriminator_candidate_map_review_acceptance_item_count"
        ]
        == 26
    )
    assert "candidate measurable systems indexed" in empirical_review[
        "ccft_empirical_discriminator_candidate_map_review_acceptance_items"
    ]
    assert "required blockers before CCFT validation preserved" in empirical_review[
        "ccft_empirical_discriminator_candidate_map_review_acceptance_items"
    ]
    assert empirical_review["empirical_claim_authorized"] == "no"
    assert empirical_review["pillar_closure_authorized"] == "no"
    _assert_registry_nonclaims(empirical_review)

    priority_packet = workstream(PRIORITY_PACKET_TARGET, payload)
    assert priority_packet["status"] == "paused"
    assert priority_packet["packet_result"] == STAGES["priority_packet"].outcome_id
    assert priority_packet["strict_packet_result"] == (
        STAGES["priority_packet"].strict_outcome_id
    )
    assert priority_packet["selected_next_target"] == PRIORITY_REVIEW_TARGET
    assert priority_packet["selected_next_target_kind"] == (
        "ccft_empirical_discriminator_candidate_priority_selection_packet_result_review"
    )
    assert priority_packet[
        "ccft_empirical_discriminator_candidate_priority_selection_action_count"
    ] == 10
    assert priority_packet[
        "ccft_empirical_discriminator_candidate_priority_selection_criteria_count"
    ] == 7
    assert priority_packet["selected_top_candidate_for_future_packet_only"] == (
        "controlled_mesoscopic_coherence_platform_candidate"
    )
    assert "rank_1_controlled_mesoscopic_coherence_platform_candidate" in (
        priority_packet["candidate_measurable_system_ranking"]
    )
    assert "risk of overclaim" in priority_packet[
        "ccft_empirical_discriminator_candidate_priority_selection_criteria"
    ]
    assert priority_packet["future_packet_preparation_only"] == "yes"
    assert priority_packet["empirical_test_executed"] == "no"
    assert priority_packet["CCFT_validated"] == "no"
    _assert_registry_nonclaims(priority_packet)

    priority_review = workstream(PRIORITY_REVIEW_TARGET, payload)
    assert priority_review["status"] == "paused"
    assert priority_review["review_result"] == STAGES["priority_review"].outcome_id
    assert priority_review["strict_review_result"] == (
        STAGES["priority_review"].strict_outcome_id
    )
    assert priority_review["prepared_packet_result"] == (
        STAGES["priority_packet"].outcome_id
    )
    assert priority_review["prepared_packet_strict_result"] == (
        STAGES["priority_packet"].strict_outcome_id
    )
    assert priority_review["selected_next_target"] == SELECTED_CANDIDATE_PACKET_TARGET
    assert priority_review["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_candidate_packet"
    )
    assert priority_review[
        "ccft_empirical_discriminator_candidate_priority_selection_review_acceptance_item_count"
    ] == 25
    assert "selected top candidate retained for future packet preparation only" in (
        priority_review[
            "ccft_empirical_discriminator_candidate_priority_selection_review_acceptance_items"
        ]
    )
    assert priority_review[
        "selected_top_discriminator_priority_accepted_for_future_packet_only"
    ] == "yes"
    assert priority_review["selected_candidate_packet_preparation_target"] == (
        SELECTED_CANDIDATE_PACKET_TARGET
    )
    assert priority_review["empirical_execution_authorized"] == "no"
    assert priority_review["empirical_test_executed"] == "no"
    assert priority_review["CCFT_validated"] == "no"
    _assert_registry_nonclaims(priority_review)

    selected_candidate_packet = workstream(SELECTED_CANDIDATE_PACKET_TARGET, payload)
    assert selected_candidate_packet["status"] == "paused"
    assert (
        selected_candidate_packet["packet_result"]
        == STAGES["selected_candidate_packet"].outcome_id
    )
    assert selected_candidate_packet["strict_packet_result"] == (
        STAGES["selected_candidate_packet"].strict_outcome_id
    )
    assert (
        selected_candidate_packet["selected_next_target"]
        == SELECTED_CANDIDATE_REVIEW_TARGET
    )
    assert selected_candidate_packet["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_candidate_packet_result_review"
    )
    assert (
        selected_candidate_packet[
            "selected_ccft_empirical_discriminator_candidate_packet_action_count"
        ]
        == 11
    )
    assert selected_candidate_packet[
        "selected_ccft_empirical_discriminator_candidate_id"
    ] == "controlled_mesoscopic_coherence_platform_candidate"
    assert selected_candidate_packet[
        "selected_ccft_empirical_discriminator_candidate_observable"
    ] == "coherence_lifetime_residual_candidate"
    assert selected_candidate_packet[
        "selected_ccft_empirical_discriminator_candidate_baseline"
    ] == "standard_open_system_decoherence_baseline_comparison"
    assert selected_candidate_packet[
        "selected_ccft_empirical_discriminator_candidate_falsifier"
    ] == "null_separation_from_baseline_with_registered_tolerances"
    assert selected_candidate_packet["priority_selection_result_review_consumed"] == (
        "yes"
    )
    assert selected_candidate_packet[
        "selected_candidate_instantiated_for_future_packet_only"
    ] == "yes"
    assert selected_candidate_packet["selected_observable_bound_as_planning_row"] == (
        "yes"
    )
    assert selected_candidate_packet["selected_baseline_bound_as_planning_row"] == (
        "yes"
    )
    assert selected_candidate_packet["selected_falsifier_bound_as_planning_row"] == (
        "yes"
    )
    assert selected_candidate_packet["empirical_execution_authorized"] == "no"
    assert selected_candidate_packet["empirical_protocol_executed"] == "no"
    assert selected_candidate_packet["selected_candidate_validation_claimed"] == "no"
    assert selected_candidate_packet["empirical_test_executed"] == "no"
    assert selected_candidate_packet["CCFT_validated"] == "no"
    _assert_registry_nonclaims(selected_candidate_packet)

    selected_candidate_review = workstream(SELECTED_CANDIDATE_REVIEW_TARGET, payload)
    assert selected_candidate_review["status"] == "paused"
    assert (
        selected_candidate_review["review_result"]
        == STAGES["selected_candidate_review"].outcome_id
    )
    assert selected_candidate_review["strict_review_result"] == (
        STAGES["selected_candidate_review"].strict_outcome_id
    )
    assert selected_candidate_review["prepared_packet_result"] == (
        STAGES["selected_candidate_packet"].outcome_id
    )
    assert selected_candidate_review["prepared_packet_strict_result"] == (
        STAGES["selected_candidate_packet"].strict_outcome_id
    )
    assert (
        selected_candidate_review["selected_next_target"]
        == TOLERANCE_REGISTRY_PACKET_TARGET
    )
    assert selected_candidate_review["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_tolerance_registry_packet"
    )
    assert (
        selected_candidate_review[
            "selected_ccft_empirical_discriminator_candidate_review_acceptance_item_count"
        ]
        == 29
    )
    assert "registered_tolerances treated as non-executed traceability placeholder only" in (
        selected_candidate_review[
            "selected_ccft_empirical_discriminator_candidate_review_acceptance_items"
        ]
    )
    assert "registered_tolerances not treated as empirically calibrated" in (
        selected_candidate_review[
            "selected_ccft_empirical_discriminator_candidate_review_acceptance_items"
        ]
    )
    assert (
        selected_candidate_review[
            "selected_candidate_packet_accepted_as_future_packet_only"
        ]
        == "yes"
    )
    assert (
        selected_candidate_review["registered_tolerances_traceability_placeholder_only"]
        == "yes"
    )
    assert selected_candidate_review["registered_tolerances_empirically_calibrated"] == (
        "no"
    )
    assert selected_candidate_review["registered_tolerances_execution_authorized"] == (
        "no"
    )
    assert selected_candidate_review[
        "registered_tolerances_empirical_claim_authorized"
    ] == "no"
    assert selected_candidate_review["empirical_protocol_design_authorized"] == "no"
    assert selected_candidate_review["empirical_execution_authorized"] == "no"
    assert selected_candidate_review["empirical_protocol_executed"] == "no"
    assert selected_candidate_review["empirical_test_executed"] == "no"
    assert selected_candidate_review["CCFT_validated"] == "no"
    _assert_registry_nonclaims(selected_candidate_review)

    tolerance_registry_packet = workstream(TOLERANCE_REGISTRY_PACKET_TARGET, payload)
    assert tolerance_registry_packet["status"] == "paused"
    assert (
        tolerance_registry_packet["packet_result"]
        == STAGES["tolerance_registry_packet"].outcome_id
    )
    assert tolerance_registry_packet["strict_packet_result"] == (
        STAGES["tolerance_registry_packet"].strict_outcome_id
    )
    assert tolerance_registry_packet["selected_next_target"] == (
        TOLERANCE_REGISTRY_REVIEW_TARGET
    )
    assert tolerance_registry_packet["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_tolerance_registry_packet_result_review"
    )
    assert (
        tolerance_registry_packet[
            "selected_ccft_empirical_discriminator_tolerance_registry_field_count"
        ]
        == 8
    )
    assert (
        tolerance_registry_packet[
            "selected_ccft_empirical_discriminator_tolerance_registry_row_count"
        ]
        == 1
    )
    assert "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0" in (
        tolerance_registry_packet[
            "selected_ccft_empirical_discriminator_tolerance_ids"
        ]
    )
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_observable_binding"
    ] == "coherence_lifetime_residual_candidate"
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_baseline_binding"
    ] == "standard_open_system_decoherence_baseline_comparison"
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_null_condition"
    ] == "null_separation_from_baseline_with_registered_tolerances"
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_source_status"
    ] == "placeholder_future_empirical_calibration_needed"
    assert tolerance_registry_packet[
        "selected_ccft_empirical_discriminator_tolerance_execution_status"
    ] == "not_executed"
    assert "confidence_interval_separation_placeholder" in (
        tolerance_registry_packet[
            "selected_ccft_empirical_discriminator_tolerance_comparison_semantics"
        ]
    )
    assert (
        tolerance_registry_packet["registered_tolerances_traceability_placeholder_only"]
        == "yes"
    )
    assert tolerance_registry_packet["registered_tolerances_empirically_calibrated"] == (
        "no"
    )
    assert tolerance_registry_packet["registered_tolerances_statistically_validated"] == (
        "no"
    )
    assert tolerance_registry_packet["registered_tolerances_execution_authorized"] == (
        "no"
    )
    assert tolerance_registry_packet[
        "registered_tolerances_empirical_claim_authorized"
    ] == "no"
    assert tolerance_registry_packet[
        "registered_tolerances_sufficient_for_execution"
    ] == "no"
    assert tolerance_registry_packet[
        "registered_tolerances_distinguish_ccft_from_baseline_claimed"
    ] == "no"
    assert tolerance_registry_packet[
        "registered_tolerances_bound_to_measurement_campaign"
    ] == "no"
    assert tolerance_registry_packet["empirical_methods_section_claimed"] == "no"
    assert tolerance_registry_packet["empirical_protocol_design_authorized"] == "no"
    assert tolerance_registry_packet["empirical_execution_authorized"] == "no"
    assert tolerance_registry_packet["empirical_test_executed"] == "no"
    assert tolerance_registry_packet["CCFT_validated"] == "no"
    _assert_registry_nonclaims(tolerance_registry_packet)

    tolerance_registry_review = workstream(TOLERANCE_REGISTRY_REVIEW_TARGET, payload)
    assert tolerance_registry_review["status"] == "paused"
    assert (
        tolerance_registry_review["review_result"]
        == STAGES["tolerance_registry_review"].outcome_id
    )
    assert tolerance_registry_review["strict_review_result"] == (
        STAGES["tolerance_registry_review"].strict_outcome_id
    )
    assert tolerance_registry_review["prepared_packet_result"] == (
        STAGES["tolerance_registry_packet"].outcome_id
    )
    assert tolerance_registry_review["prepared_packet_strict_result"] == (
        STAGES["tolerance_registry_packet"].strict_outcome_id
    )
    assert tolerance_registry_review["selected_next_target"] == BASELINE_SEMANTICS_PACKET_TARGET
    assert tolerance_registry_review["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet"
    )
    assert (
        tolerance_registry_review[
            "selected_ccft_empirical_discriminator_tolerance_registry_review_acceptance_item_count"
        ]
        == 35
    )
    assert "registered_tolerances not treated as empirically calibrated" in (
        tolerance_registry_review[
            "selected_ccft_empirical_discriminator_tolerance_registry_review_acceptance_items"
        ]
    )
    assert "tolerance row not accepted as a statistical decision rule" in (
        tolerance_registry_review[
            "selected_ccft_empirical_discriminator_tolerance_registry_review_acceptance_items"
        ]
    )
    assert (
        tolerance_registry_review[
            "tolerance_registry_packet_accepted_as_traceability_only"
        ]
        == "yes"
    )
    assert (
        tolerance_registry_review[
            "tolerance_registry_rows_accepted_as_non_executed_only"
        ]
        == "yes"
    )
    assert (
        tolerance_registry_review[
            "comparison_semantics_accepted_as_placeholders_only"
        ]
        == "yes"
    )
    assert tolerance_registry_review["null_condition_retained_as_default"] == "yes"
    assert (
        tolerance_registry_review[
            "future_empirical_calibration_required_before_claim"
        ]
        == "yes"
    )
    assert tolerance_registry_review["tolerance_row_accepted_as_test_protocol"] == (
        "no"
    )
    assert tolerance_registry_review[
        "tolerance_row_accepted_as_effect_size_threshold"
    ] == "no"
    assert tolerance_registry_review[
        "tolerance_row_accepted_as_statistical_decision_rule"
    ] == "no"
    assert tolerance_registry_review["tolerance_row_accepted_as_experimental_design"] == (
        "no"
    )
    assert tolerance_registry_review["registered_tolerances_empirically_calibrated"] == (
        "no"
    )
    assert tolerance_registry_review["registered_tolerances_statistically_validated"] == (
        "no"
    )
    assert tolerance_registry_review["registered_tolerances_sufficient_for_execution"] == (
        "no"
    )
    assert tolerance_registry_review[
        "registered_tolerances_distinguish_ccft_from_baseline_claimed"
    ] == "no"
    assert tolerance_registry_review[
        "registered_tolerances_bound_to_measurement_campaign"
    ] == "no"
    assert tolerance_registry_review["selected_next_planning_packet_target"] == (
        BASELINE_SEMANTICS_PACKET_TARGET
    )
    _assert_registry_nonclaims(tolerance_registry_review)

    baseline_packet = workstream(BASELINE_SEMANTICS_PACKET_TARGET, payload)
    assert baseline_packet["status"] == "paused"
    assert baseline_packet["packet_result"] == STAGES["baseline_semantics_packet"].outcome_id
    assert baseline_packet["strict_packet_result"] == (
        STAGES["baseline_semantics_packet"].strict_outcome_id
    )
    assert baseline_packet["selected_next_target"] == FINAL_PREVIOUS_TARGET
    assert baseline_packet["selected_next_target_kind"] == (
        "selected_ccft_empirical_discriminator_baseline_comparison_semantics_packet_result_review"
    )
    assert (
        baseline_packet[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_field_count"
        ]
        == 10
    )
    assert (
        baseline_packet[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_row_count"
        ]
        == 1
    )
    assert "BSEM-CCFT-MESO-COH-LIFETIME-v0" in (
        baseline_packet[
            "selected_ccft_empirical_discriminator_baseline_semantics_ids"
        ]
    )
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_baseline_candidate_binding"
    ] == "controlled_mesoscopic_coherence_platform_candidate"
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_baseline_observable_binding"
    ] == "coherence_lifetime_residual_candidate"
    assert baseline_packet["selected_ccft_empirical_discriminator_baseline_binding"] == (
        "standard_open_system_decoherence_baseline_comparison"
    )
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_baseline_null_default"
    ] == "null_separation_from_baseline_with_registered_tolerances"
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_baseline_tolerance_binding"
    ] == "TOL-CCFT-MESO-COH-LIFETIME-RESIDUAL-v0"
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_residual_definition_status"
    ] == "placeholder_future_refinement_needed"
    assert baseline_packet[
        "selected_ccft_empirical_discriminator_comparison_direction_status"
    ] == "placeholder_direction_not_selected"
    assert baseline_packet["baseline_comparison_semantics_packet_prepared"] == "yes"
    assert baseline_packet["baseline_comparison_semantics_rows_registered"] == "yes"
    assert baseline_packet["baseline_semantics_logic_only"] == "yes"
    assert baseline_packet["baseline_complete_claimed"] == "no"
    assert baseline_packet["baseline_experimentally_fitted"] == "no"
    assert baseline_packet["residual_observed"] == "no"
    assert baseline_packet["tolerance_determines_significance"] == "no"
    assert baseline_packet["ccft_measurable_separation_predicted"] == "no"
    assert baseline_packet["candidate_ready_for_execution"] == "no"
    assert baseline_packet["baseline_separation_claimed"] == "no"
    assert baseline_packet["empirical_protocol_authorized"] == "no"
    assert baseline_packet["empirical_protocol_defined"] == "no"
    assert baseline_packet["statistical_validation_claimed"] == "no"
    assert baseline_packet["statistical_decision_rule_defined"] == "no"
    assert baseline_packet["effect_size_threshold_defined"] == "no"
    assert baseline_packet["execution_readiness_claimed"] == "no"
    _assert_registry_nonclaims(baseline_packet)

    baseline_review = workstream(FINAL_PREVIOUS_TARGET, payload)
    assert baseline_review["status"] == "paused"
    assert baseline_review["review_result"] == FINAL_OUTCOME
    assert baseline_review["strict_review_result"] == FINAL_STRICT_OUTCOME
    assert baseline_review["prepared_packet_result"] == (
        STAGES["baseline_semantics_packet"].outcome_id
    )
    assert baseline_review["prepared_packet_strict_result"] == (
        STAGES["baseline_semantics_packet"].strict_outcome_id
    )
    assert baseline_review["selected_next_target"] == FINAL_LIVE_TARGET
    assert baseline_review["selected_next_target_kind"] == FINAL_KIND
    assert (
        baseline_review[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_review_acceptance_item_count"
        ]
        == 34
    )
    assert "baseline not accepted as complete" in (
        baseline_review[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_review_acceptance_items"
        ]
    )
    assert "experimental protocol readiness not accepted" in (
        baseline_review[
            "selected_ccft_empirical_discriminator_baseline_comparison_semantics_review_acceptance_items"
        ]
    )
    assert baseline_review[
        "baseline_comparison_semantics_packet_accepted_as_logic_only"
    ] == "yes"
    assert baseline_review[
        "baseline_semantics_rows_accepted_as_non_executed_only"
    ] == "yes"
    assert baseline_review[
        "residual_definition_status_accepted_as_placeholder_only"
    ] == "yes"
    assert baseline_review[
        "comparison_direction_accepted_as_placeholder_only"
    ] == "yes"
    assert baseline_review["baseline_not_accepted_as_complete"] == "yes"
    assert baseline_review["baseline_adequacy_accepted"] == "no"
    assert baseline_review["baseline_empirical_fit_quality_accepted"] == "no"
    assert baseline_review["statistical_decision_rule_validity_accepted"] == "no"
    assert baseline_review["observed_separation_accepted"] == "no"
    assert baseline_review["ccft_predicted_separation_accepted"] == "no"
    assert baseline_review["experimental_protocol_readiness_accepted"] == "no"
    assert baseline_review["selected_next_planning_packet_target"] == FINAL_LIVE_TARGET
    _assert_registry_nonclaims(baseline_review)

    active = workstream(FINAL_LIVE_TARGET, payload)
    assert active["status"] == "active"
    assert active["active_lane"] == FINAL_LIVE_TARGET
    assert active["authorized_next_strict_target"] == FINAL_LIVE_TARGET
    assert active["consumed_target"] == FINAL_PREVIOUS_TARGET
    assert active["authorization_evidence"] == FINAL_EVIDENCE
    assert active["report"] == FINAL_REPORT
    assert active["review_result"] == FINAL_OUTCOME
    assert active["strict_review_result"] == FINAL_STRICT_OUTCOME
    assert active["prepared_packet_result"] == (
        STAGES["baseline_semantics_packet"].outcome_id
    )
    assert active["prepared_packet_strict_result"] == (
        STAGES["baseline_semantics_packet"].strict_outcome_id
    )
    assert active["selected_next_target"] == "PENDING"
    assert active["selected_next_target_kind"] == "PENDING"
    assert active["suggested_next_packet_target"] == FINAL_LIVE_TARGET
    assert active["suggested_next_packet_kind"] == FINAL_KIND
    assert active["ccft_empirical_discriminator_candidate_map_target_count"] == 11
    assert active[
        "ccft_empirical_discriminator_candidate_priority_selection_action_count"
    ] == 10
    assert active["selected_top_candidate_for_future_packet_only"] == (
        "controlled_mesoscopic_coherence_platform_candidate"
    )
    assert active["C_k_action_embedding_authorized"] == "no"
    assert active["C_k_variation_authorized"] == "no"
    assert active["empirical_discriminator_claims_authorized"] == "no"
    assert active["empirical_claim_authorized"] == "no"
    assert active["pillar_closure_authorized"] == "no"
    assert active["empirical_test_executed"] == "no"
    assert active["empirical_execution_authorized"] == "no"
    assert (
        active["selected_ccft_empirical_discriminator_candidate_packet_action_count"]
        == 11
    )
    assert active["selected_ccft_empirical_discriminator_candidate_id"] == (
        "controlled_mesoscopic_coherence_platform_candidate"
    )
    assert active["selected_ccft_empirical_discriminator_candidate_observable"] == (
        "coherence_lifetime_residual_candidate"
    )
    assert active["selected_ccft_empirical_discriminator_candidate_baseline"] == (
        "standard_open_system_decoherence_baseline_comparison"
    )
    assert active["selected_ccft_empirical_discriminator_candidate_falsifier"] == (
        "null_separation_from_baseline_with_registered_tolerances"
    )
    assert active["priority_selection_result_review_consumed"] == "yes"
    assert active["selected_candidate_instantiated_for_future_packet_only"] == "yes"
    assert active["selected_observable_bound_as_planning_row"] == "yes"
    assert active["selected_baseline_bound_as_planning_row"] == "yes"
    assert active["selected_falsifier_bound_as_planning_row"] == "yes"
    assert active["selected_candidate_packet_accepted_as_future_packet_only"] == "yes"
    assert active["registered_tolerances_traceability_placeholder_only"] == "yes"
    assert active["registered_tolerances_empirically_calibrated"] == "no"
    assert active["registered_tolerances_statistically_validated"] == "no"
    assert active["registered_tolerances_execution_authorized"] == "no"
    assert active["registered_tolerances_empirical_claim_authorized"] == "no"
    assert active["registered_tolerances_sufficient_for_execution"] == "no"
    assert (
        active["registered_tolerances_distinguish_ccft_from_baseline_claimed"]
        == "no"
    )
    assert active["registered_tolerances_bound_to_measurement_campaign"] == "no"
    assert active["tolerance_registry_result_review_consumed"] == "yes"
    assert active["tolerance_registry_review_result"] == (
        STAGES["tolerance_registry_review"].outcome_id
    )
    assert active["tolerance_registry_review_strict_result"] == (
        STAGES["tolerance_registry_review"].strict_outcome_id
    )
    assert active["baseline_comparison_semantics_packet_prepared"] == "yes"
    assert active["baseline_comparison_semantics_rows_registered"] == "yes"
    assert active["baseline_semantics_logic_only"] == "yes"
    assert active["baseline_complete_claimed"] == "no"
    assert active["baseline_experimentally_fitted"] == "no"
    assert active["residual_observed"] == "no"
    assert active["tolerance_determines_significance"] == "no"
    assert active["ccft_measurable_separation_predicted"] == "no"
    assert active["candidate_ready_for_execution"] == "no"
    assert active["baseline_separation_claimed"] == "no"
    assert active["empirical_protocol_authorized"] == "no"
    assert active["empirical_protocol_defined"] == "no"
    assert active["statistical_validation_claimed"] == "no"
    assert active["statistical_decision_rule_defined"] == "no"
    assert active["effect_size_threshold_defined"] == "no"
    assert active["execution_readiness_claimed"] == "no"
    assert active["baseline_comparison_semantics_packet_accepted_as_logic_only"] == "yes"
    assert active["baseline_semantics_rows_accepted_as_non_executed_only"] == "yes"
    assert active["residual_definition_status_accepted_as_placeholder_only"] == "yes"
    assert active["comparison_direction_accepted_as_placeholder_only"] == "yes"
    assert active["baseline_not_accepted_as_complete"] == "yes"
    assert active["baseline_adequacy_accepted"] == "no"
    assert active["baseline_empirical_fit_quality_accepted"] == "no"
    assert active["statistical_decision_rule_validity_accepted"] == "no"
    assert active["observed_separation_accepted"] == "no"
    assert active["ccft_predicted_separation_accepted"] == "no"
    assert active["experimental_protocol_readiness_accepted"] == "no"
    assert active["empirical_methods_section_claimed"] == "no"
    assert active["empirical_protocol_design_authorized"] == "no"
    assert active["empirical_protocol_executed"] == "no"
    assert active["selected_candidate_validation_claimed"] == "no"
    assert active["future_packet_preparation_only"] == "yes"
    assert active["CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0_prepared"] == "yes"
    assert active["later_ccft_artifacts_fully_populated"] == "yes"
    _assert_registry_nonclaims(active)


def test_post_phi_transport_ccft_public_mirrors_contain_outcome_tokens() -> None:
    for path in PUBLIC_SURFACES:
        text = read_text(path)
        assert FINAL_LIVE_TARGET in text
        assert FINAL_PREVIOUS_TARGET in text
        assert FINAL_OUTCOME in text
        assert FINAL_STRICT_OUTCOME in text
        assert LEAN_STATUS_WORDING in text
        for stage_key in ORDERED_STAGE_KEYS:
            spec = STAGES[stage_key]
            assert spec.outcome_id in text, f"{path} missing {spec.outcome_id}"
            assert spec.strict_outcome_id in text, (
                f"{path} missing {spec.strict_outcome_id}"
            )

    for doc in PAPER_DOCS:
        text = read_text(REPO_ROOT / doc)
        assert LOCAL_PHI_THEOREM_LINKAGE_TRIAD_LABEL in text
        assert "CCFT" in text
        assert "no proof execution" in text
        assert "no CCFT validation" in text
        assert "no master-action promotion" in text


def test_post_phi_transport_ccft_focused_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_post_phi_transport_ccft_chain_gate.py"
    )
