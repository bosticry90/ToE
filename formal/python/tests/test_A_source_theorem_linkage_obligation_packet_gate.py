from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_frontier_matches_registry,
    assert_historical_target_recorded,
    assert_public_surfaces_match_registry,
)
from formal.python.tools.A_source_theorem_linkage_obligation_packet_report import (
    BOUNDARY_ITEMS,
    C_SOURCE_A_CONSTRAINT_CANDIDATE,
    C_SOURCE_A_SHORT_FORM,
    C_SOURCE_A_TARGET_STATEMENT,
    DEFAULT_OUT,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PACKET_SCOPE_RECORD,
    PSI_A_SOURCED_MAXWELL_ROUTE,
    PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
    SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONDITION,
    STANDALONE_A_ROUTE,
    STRICT_PACKET_RESULT,
    WATCH_ITEMS,
    build_A_source_theorem_linkage_obligation_packet,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "A_source_theorem_linkage_obligation_packet_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
CURRENT_TARGET_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CurrentTarget.lean"
)
QFTGR_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_AUTHORITY_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8-sig")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def consumed_target() -> str:
    return "prepare_A_source_theorem_linkage_obligation_packet"


def test_A_source_theorem_linkage_obligation_packet_files_exist() -> None:
    for path in [
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_A_source_theorem_linkage_obligation_packet_scopes_prior_A_route() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["artifact_id"] == SCHEMA_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["packet_prepared"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_result"] == OUTCOME_ID
    assert packet["strict_packet_result"] == STRICT_PACKET_RESULT
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == consumed_target()
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["packet_scope_record"] == PACKET_SCOPE_RECORD
    assert packet["watch_items"] == WATCH_ITEMS
    assert packet["boundary_items"] == BOUNDARY_ITEMS
    assert build_A_source_theorem_linkage_obligation_packet() == packet


def test_A_source_theorem_linkage_obligation_packet_freezes_vacuum_source_statement() -> None:
    packet = _json(DEFAULT_OUT)

    assert packet["standalone_A_sector_route"] == STANDALONE_A_ROUTE
    assert packet["standalone_A_sector_route_preserved"] is True
    assert packet["C_source_A_constraint_candidate"] == C_SOURCE_A_CONSTRAINT_CANDIDATE
    assert packet["C_source_A_short_form"] == C_SOURCE_A_SHORT_FORM
    assert packet["C_source_A_target_statement"] == C_SOURCE_A_TARGET_STATEMENT
    assert packet["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert packet["accepted_A_sector_source_equation_to_freeze"] == (
        "nabla_mu T_A^{mu nu} = 0"
    )
    assert packet["stress_energy_divergence_route"] == (
        "nabla_mu T_A^{mu nu} = - F^{nu}{}_{alpha} nabla_mu F^{mu alpha}"
    )
    assert packet["vacuum_euler_lagrange_route"] == "nabla_mu F^{mu nu} = 0"
    assert packet["on_shell_vacuum_conservation_route"] == (
        "nabla_mu T_A^{mu nu} = - F^{nu}{}_{alpha} nabla_mu F^{mu alpha} "
        "and nabla_mu F^{mu nu} = 0 imply nabla_mu T_A^{mu nu} = 0"
    )
    assert packet["psi_A_sourced_maxwell_route"] == PSI_A_SOURCED_MAXWELL_ROUTE
    assert packet["psi_A_sourced_route_substituted"] is False
    assert packet["do_not_silently_substitute_psi_A_sourced_Maxwell_route"] is True
    assert packet["route_contamination_guard"] == PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD


def test_A_source_theorem_linkage_obligation_packet_preserves_boundaries() -> None:
    packet = _json(DEFAULT_OUT)

    for flag in [
        "proof_execution_authorized",
        "proof_attempt_executed",
        "theorem_execution_authorized",
        "theorem_discharged",
        "theorem_linkage_obligation_discharged",
        "C_source_A_discharged",
        "A_source_theorem_linkage_obligation_discharged",
        "gap_1_through_gap_8_discharged",
        "general_C_k_closure",
        "C_k_dynamical_law_status",
        "C_k_rule_promoted",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "action_embedding_claimed",
        "action_variation_executed",
        "A_sector_closure_claimed",
        "sourced_maxwell_closure_claimed",
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert packet[flag] is False, flag

    assert packet["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_REVIEW
    assert (
        packet["full_toeformal_aggregate_status_for_packet"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert packet["scoped_lean_targets_status_for_packet"] == "PASSED_SERIAL_RERUN"
    assert packet["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(packet)


def test_A_source_theorem_linkage_obligation_packet_rotates_to_review() -> None:
    registry = _json(REGISTRY_PATH)
    evidence = _rel(LEAN_PACKET_PATH)
    report = _rel(DEFAULT_OUT)

    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_public_surfaces_match_registry()

    is_current = assert_historical_target_recorded(
        payload=registry,
        previous_target=consumed_target(),
        live_target=NEXT_TARGET,
        evidence=evidence,
        lane=NEXT_TARGET,
    )

    assert consumed_target() in registry["completed_targets"]
    assert consumed_target() in registry["consumed_targets"]
    assert consumed_target() in registry["paused_lanes"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, consumed_target())
    assert consumed["status"] == "paused"
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["packet_result"] == OUTCOME_ID
    assert consumed["strict_packet_result"] == STRICT_PACKET_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert consumed["psi_A_sourced_route_substituted"] == "no"
    assert consumed["proof_attempt_executed"] == "no"
    assert consumed["theorem_discharged"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    review_row = _workstream(registry, NEXT_TARGET)
    if is_current:
        assert review_row["status"] == "active"
        assert review_row["workstream_id"] == NEXT_TARGET
        assert review_row["active_lane"] == NEXT_TARGET
        assert review_row["authorization_evidence"] == evidence
        assert review_row["authorized_next_strict_target"] == NEXT_TARGET
        assert review_row["report"] == report
        assert review_row["consumed_target"] == consumed_target()
        assert review_row["packet_result"] == OUTCOME_ID
        assert review_row["strict_packet_result"] == STRICT_PACKET_RESULT
        assert review_row["review_result"] == "PENDING"
        assert review_row["selected_next_target"] == "PENDING"
    else:
        assert review_row["status"] == "paused"
        assert review_row["prepared_packet_result"] == OUTCOME_ID
        assert review_row["selected_next_target"] == (
            "prepare_A_source_theorem_linkage_attempt_from_standalone_A_route"
        )
    assert review_row["selected_obligation"] == "C_source^A theorem-linkage obligation"
    assert review_row["source_admissibility_condition"] == SOURCE_ADMISSIBILITY_CONDITION
    assert review_row["psi_A_sourced_route_substituted"] == "no"
    assert review_row["proof_execution_authorized"] == "no"
    assert review_row["C_source_A_discharged"] == "no"
    assert review_row["sourced_maxwell_closure_claimed"] == "no"
    assert review_row["full_maxwell_closure_claimed"] == "no"
    assert review_row["qft_gr_closure_claimed"] == "no"
    assert review_row["master_action_promoted"] == "no"


def test_A_source_theorem_linkage_obligation_packet_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_PATH,
            CURRENT_TARGET_PATH,
            CURRENT_AUTHORITY_PATH,
            TOE_FORMAL_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            ROADMAP_PATH,
            STRICT_MAP_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        STRICT_PACKET_RESULT,
        PACKET_CLASSIFICATION,
        "ASourceTheoremLinkageObligationPacket",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        C_SOURCE_A_SHORT_FORM,
        SOURCE_ADMISSIBILITY_CONDITION,
        PSI_A_SOURCED_MAXWELL_ROUTE,
        PSI_A_SOURCED_ROUTE_CONTAMINATION_GUARD,
        "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_OUTCOME_v0",
        "A_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_NONCLAIM_BOUNDARY_v0",
        "do not silently substitute",
        "no proof execution",
        "no theorem discharge",
        "no A-sector closure",
        "no sourced Maxwell closure",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no general C_k closure",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_A_source_theorem_linkage_obligation_packet_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_A_source_theorem_linkage_obligation_packet_gate.py"
    )
