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


FINAL_LIVE_TARGET = "review_ccft_full_variational_action_program_packet_result"
FINAL_PREVIOUS_TARGET = "prepare_ccft_full_variational_action_program_packet"
FINAL_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "CCFTFullVariationalActionProgramPacket.lean"
)
FINAL_REPORT = (
    "formal/docs/release/"
    "CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_PACKET_20260702_v0.json"
)
FINAL_OUTCOME = STAGES["variational_packet"].outcome_id
FINAL_STRICT_OUTCOME = STAGES["variational_packet"].strict_outcome_id
FINAL_KIND = "ccft_full_variational_action_program_packet_result_review"
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
}

PAPER_DOCS = (
    "formal/docs/paper/TOE_COHERENCE_ADMISSIBILITY_BRIDGE_HYPOTHESIS_v0.md",
    "formal/docs/paper/TOE_COHERENCE_ADMISSIBILITY_BRIDGE_ROADMAP_v1.md",
    "formal/docs/paper/CCFT_TO_TOE_OBJECT_CROSSWALK_v0.md",
    "formal/docs/paper/CCFT_CK_ADMISSIBILITY_OBLIGATION_INDEX_v0.md",
    "formal/docs/paper/CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0.md",
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
        FINAL_PREVIOUS_TARGET
    )
    assert STAGES["variational_packet"].selected_next_target == FINAL_LIVE_TARGET


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
    assert ck_review["selected_next_target"] == FINAL_PREVIOUS_TARGET
    assert ck_review["selected_next_target_kind"] == (
        "ccft_full_variational_action_program_packet"
    )
    assert ck_review["prepared_packet_result"] == STAGES["ck_index_packet"].outcome_id
    assert ck_review["prepared_packet_strict_result"] == (
        STAGES["ck_index_packet"].strict_outcome_id
    )
    _assert_registry_nonclaims(ck_review)

    prepared_packet = workstream(FINAL_PREVIOUS_TARGET, payload)
    assert prepared_packet["status"] == "paused"
    assert prepared_packet["packet_result"] == FINAL_OUTCOME
    assert prepared_packet["strict_packet_result"] == FINAL_STRICT_OUTCOME
    assert prepared_packet["selected_next_target"] == FINAL_LIVE_TARGET
    assert prepared_packet["selected_next_target_kind"] == FINAL_KIND
    assert prepared_packet["ccft_full_variational_action_program_target_count"] == 13
    assert prepared_packet["C_k_action_embedding_authorized"] == "no"
    assert prepared_packet["C_k_variation_authorized"] == "no"
    assert prepared_packet["empirical_discriminator_claims_authorized"] == "no"
    _assert_registry_nonclaims(prepared_packet)

    active = workstream(FINAL_LIVE_TARGET, payload)
    assert active["status"] == "active"
    assert active["active_lane"] == FINAL_LIVE_TARGET
    assert active["authorized_next_strict_target"] == FINAL_LIVE_TARGET
    assert active["consumed_target"] == FINAL_PREVIOUS_TARGET
    assert active["authorization_evidence"] == FINAL_EVIDENCE
    assert active["report"] == FINAL_REPORT
    assert active["packet_result"] == FINAL_OUTCOME
    assert active["strict_packet_result"] == FINAL_STRICT_OUTCOME
    assert active["review_result"] == "PENDING"
    assert active["strict_review_result"] == "PENDING"
    assert active["selected_next_target"] == "PENDING"
    assert active["selected_next_target_kind"] == "PENDING"
    assert active["packet_review_target"] == FINAL_LIVE_TARGET
    assert active["packet_review_target_kind"] == FINAL_KIND
    assert active["ccft_full_variational_action_program_target_count"] == 13
    assert active["C_k_action_embedding_authorized"] == "no"
    assert active["C_k_variation_authorized"] == "no"
    assert active["empirical_discriminator_claims_authorized"] == "no"
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
