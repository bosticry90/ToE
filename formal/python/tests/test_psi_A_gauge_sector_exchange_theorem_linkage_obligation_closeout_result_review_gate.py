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
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_report import (
    CLOSEOUT_RESULT,
    DEFAULT_OUT as CLOSEOUT_OUT,
    LEAN_PACKET_PATH as CLOSEOUT_LEAN_PACKET_PATH,
    OUTCOME_ID as CLOSEOUT_OUTCOME,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review_report import (
    ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    ACCEPTED_REVIEW_FINDINGS,
    ACCEPTED_SOURCED_MAXWELL_ROUTE,
    CURRENT_OBJECT,
    DEFAULT_OUT,
    FIELD_STRENGTH_OBJECT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LIKELY_NEXT_OBLIGATION,
    LIKELY_NEXT_OBLIGATION_REASON,
    LOCAL_DEPENDENCY_CHAIN,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REVIEW_RESULT,
    ROUTE_STATEMENT,
    SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    STRICT_REVIEW_RESULT,
    SYNTHESIS_TARGET_REASON,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    T_A_POLICY,
    WATCH_ITEMS,
    build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review_report.py"
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


def _workstreams(target: str, registry: dict, *, status: str | None = None) -> list[dict]:
    rows = [
        row
        for row in registry["workstreams"]
        if row.get("workstream_id") == target
        and (status is None or row.get("status") == status)
    ]
    assert rows, f"missing workstream {target!r} with status {status!r}"
    return rows


def consumed_target() -> str:
    return "review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result"


def test_psi_A_gauge_exchange_closeout_result_review_files_exist() -> None:
    for path in [
        CLOSEOUT_OUT,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        QFTGR_PATH,
        CURRENT_TARGET_PATH,
        CURRENT_AUTHORITY_PATH,
    ]:
        assert path.exists(), path


def test_psi_A_gauge_exchange_closeout_result_review_accepts_closeout() -> None:
    review = _json(DEFAULT_OUT)

    assert review["artifact_id"] == SCHEMA_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["packet_id"] == PACKET_ID
    assert review["prepared"] is True
    assert review["accepted"] is True
    assert review["reviewed"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["review_result"] == REVIEW_RESULT
    assert review["packet_result"] == OUTCOME_ID
    assert review["strict_review_result"] == STRICT_REVIEW_RESULT
    assert review["packet_classification"] == PACKET_CLASSIFICATION
    assert review["consumed_target"] == consumed_target()
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert review["synthesis_target_authorized"] is True
    assert review["synthesis_packet_prepared"] is False
    assert review["synthesis_target_reason"] == SYNTHESIS_TARGET_REASON
    assert review["likely_next_obligation"] == LIKELY_NEXT_OBLIGATION
    assert review["likely_next_obligation_reason"] == LIKELY_NEXT_OBLIGATION_REASON
    assert (
        build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review()
        == review
    )


def test_psi_A_gauge_exchange_closeout_result_review_preserves_boundary() -> None:
    review = _json(DEFAULT_OUT)

    assert review["accepted_review_findings"] == ACCEPTED_REVIEW_FINDINGS
    assert review["closeout_outcome"] == CLOSEOUT_RESULT
    assert review["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert review["target_rule"] == TARGET
    assert review["T_A_policy"] == T_A_POLICY
    assert review["field_strength_object"] == FIELD_STRENGTH_OBJECT
    assert review["current_object"] == CURRENT_OBJECT
    assert review["accepted_sourced_maxwell_route"] == ACCEPTED_SOURCED_MAXWELL_ROUTE
    assert review["accepted_gauge_stress_energy_divergence_identity"] == (
        ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
    )
    assert review["route_statement"] == ROUTE_STATEMENT
    assert review["watch_items"] == WATCH_ITEMS
    assert review["local_dependency_chain"] == LOCAL_DEPENDENCY_CHAIN
    assert review["gauge_sector_exchange_closeout_accepted"] is True
    assert review["gauge_exchange_linked_to_sourced_maxwell_route"] is True
    assert review["gauge_exchange_route_constructed"] is True
    assert review["gauge_exchange_derived"] is True
    assert review["same_F_and_J_objects_preserved"] is True
    assert review["sourced_maxwell_route_used"] is True
    assert review["gauge_stress_energy_divergence_identity_used"] is True
    assert review["watch_items_preserved"] is True
    assert review["review_executes_new_proof"] is False
    assert review["proof_execution_authorized"] is False

    for key in [
        "full_maxwell_closure_claimed",
        "em_qft_closure_claimed",
        "qft_gr_closure_claimed",
        "gr_qm_closure_claimed",
        "general_C_k_closure",
        "general_C_k_theorem_linkage_closure",
        "C_k_dynamical_law_status",
        "gap_1_through_gap_8_discharged",
        "rule_promoted",
        "C_k_action_embedding_claimed",
        "C_k_action_variation_executed",
        "empirical_validation_claimed",
        "seam_closure_claim",
        "master_action_promoted",
    ]:
        assert review[key] is False, key


def test_psi_A_gauge_exchange_closeout_result_review_records_lean_status() -> None:
    review = _json(DEFAULT_OUT)

    assert review["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_REVIEW
    assert (
        review["full_toeformal_aggregate_status_for_review"]
        == FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
    )
    assert (
        review["scoped_lean_targets_status_for_review"]
        == SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
    )
    assert review["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(review)


def test_psi_A_gauge_exchange_closeout_result_review_rotates_to_synthesis() -> None:
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

    closeout = _workstreams(
        "prepare_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout",
        registry,
        status="paused",
    )[-1]
    assert closeout["authorization_evidence"] == _rel(CLOSEOUT_LEAN_PACKET_PATH)
    assert closeout["report"] == _rel(CLOSEOUT_OUT)
    assert closeout["closeout_result"] == CLOSEOUT_OUTCOME

    consumed = _workstreams(consumed_target(), registry, status="paused")[-1]
    assert consumed["authorization_evidence"] == evidence
    assert consumed["report"] == report
    assert consumed["review_result"] == OUTCOME_ID
    assert consumed["strict_review_result"] == STRICT_REVIEW_RESULT
    assert consumed["selected_next_target"] == NEXT_TARGET
    assert consumed["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert consumed["gauge_sector_exchange_closeout_accepted"] == "yes"
    assert consumed["gauge_exchange_linked_to_sourced_maxwell_route"] == "yes"
    assert consumed["same_F_and_J_objects_preserved"] == "yes"
    assert consumed["synthesis_target_authorized"] == "yes"
    assert consumed["synthesis_packet_prepared"] == "no"
    assert consumed["general_C_k_theorem_linkage_closure"] == "no"
    assert consumed["rule_promoted"] == "no"
    assert consumed["master_action_promoted"] == "no"

    if is_current:
        active = active_workstream(registry)
        assert active["status"] == "active"
        assert active["workstream_id"] == NEXT_TARGET
        assert active["active_lane"] == NEXT_TARGET
        assert active["authorization_evidence"] == evidence
        assert active["report"] == report
        assert active["authorized_next_strict_target"] == NEXT_TARGET
        assert active["consumed_target"] == consumed_target()
        assert active["review_result"] == OUTCOME_ID
        assert active["strict_review_result"] == STRICT_REVIEW_RESULT
        assert active["packet_result"] == "PENDING"
        assert active["selected_next_target"] == "PENDING"
        assert active["local_dependency_chain"] == (
            "C_exchange = 0 depends on total conservation; total conservation depends "
            "on matter-sector exchange and gauge-sector exchange; matter-sector exchange "
            "depends on Dirac-pair route; gauge-sector exchange depends on "
            "stress-divergence identity plus sourced Maxwell route"
        )
        assert active["synthesis_target_authorized"] == "yes"
        assert active["synthesis_packet_prepared"] == "no"
        assert active["proof_execution_authorized"] == "no"
        assert active["rule_promoted"] == "no"
        assert active["master_action_promoted"] == "no"
    else:
        historical = _workstreams(NEXT_TARGET, registry, status="paused")[-1]
        assert historical["consumed_target"] == consumed_target()
        assert historical["synthesis_target_authorized"] == "yes"
        assert historical["synthesis_packet_prepared"] in {"no", "yes"}
        assert historical["proof_execution_authorized"] == "no"
        assert historical["rule_promoted"] == "no"
        assert historical["master_action_promoted"] == "no"


def test_psi_A_gauge_exchange_closeout_result_review_mirrors() -> None:
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
        STRICT_REVIEW_RESULT,
        PACKET_CLASSIFICATION,
        "PsiAGaugeSectorExchangeTheoremLinkageObligationCloseoutResultReview",
        consumed_target(),
        NEXT_TARGET,
        NEXT_TARGET_KIND,
        LIKELY_NEXT_OBLIGATION,
        TARGET,
        THEOREM_TARGET_STATEMENT,
        ROUTE_STATEMENT,
        LEAN_STATUS_WORDING_FOR_REVIEW,
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0",
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_CLOSEOUT_RESULT_REVIEW_NONCLAIM_BOUNDARY_v0",
        "gauge-sector exchange theorem-linkage closeout accepted",
        "gauge exchange linked to stress-divergence identity plus sourced Maxwell route",
        "same F and J objects preserved",
        "sign and index conventions preserved",
        "watch items preserved",
        "no full Maxwell closure",
        "no EM-QFT closure",
        "no QFT-GR closure",
        "no GR-QM closure",
        "no general C_k closure",
        "no C_k dynamical-law status",
        "no empirical validation",
        "no master-action promotion",
    ]:
        assert token in joined, token


def test_psi_A_gauge_exchange_closeout_result_review_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_gauge_sector_exchange_theorem_linkage_obligation_closeout_result_review_gate.py"
    )
