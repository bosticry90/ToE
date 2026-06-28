from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_execution_report import (
    ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    ACCEPTED_SOURCED_MAXWELL_ROUTE,
    DEFAULT_OUT,
    EXECUTION_RESULT,
    LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_EXECUTION,
    LEAN_THEOREM_NAME,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_ID,
    PLAIN_MEANING,
    ROUTE_GIVEN,
    ROUTE_STEPS,
    SCHEMA_ID,
    STRICT_EXECUTION_RESULT,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    WATCH_ITEMS,
    build_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_execution,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
CURRENT_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CURRENT_TARGET_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CurrentTarget.lean"
)
QFTGR_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_AUTHORITY_LEAN = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "CurrentAuthority.lean"
)
AGGREGATE_LEAN = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"

CONSUMED_TARGET = (
    "execute_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
)
RESULT_REVIEW_TARGET = NEXT_TARGET
EXECUTION_REPORT_REL = (
    "formal/docs/release/PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_"
    "MAXWELL_ROUTE_EXECUTION_20260628_v0.json"
)
EXECUTION_LEAN_REL = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteExecution.lean"
)


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _workstream(target: str, registry: dict, *, status: str | None = None) -> dict:
    rows = [
        row
        for row in registry["workstreams"]
        if row.get("workstream_id") == target and (status is None or row.get("status") == status)
    ]
    assert rows, f"missing workstream {target!r} with status {status!r}"
    return rows[-1]


def test_psi_A_gauge_exchange_attempt_execution_files_exist() -> None:
    assert DEFAULT_OUT.exists()
    assert LEAN_PACKET_PATH.exists()


def test_psi_A_gauge_exchange_attempt_execution_report_matches_builder() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["artifact_id"] == SCHEMA_ID
    assert execution["schema_id"] == SCHEMA_ID
    assert execution["packet_id"] == PACKET_ID
    assert execution["accepted"] is True
    assert execution["executed"] is True
    assert execution["outcome_id"] == OUTCOME_ID
    assert execution["packet_result"] == EXECUTION_RESULT
    assert execution["execution_result"] == EXECUTION_RESULT
    assert execution["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert execution["selected_next_target"] == NEXT_TARGET
    assert execution["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert (
        build_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_execution()
        == execution
    )


def test_psi_A_gauge_exchange_attempt_execution_constructs_route() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["attempt_type"] == "sourced-Maxwell gauge-sector exchange execution"
    assert execution["input_route"] == (
        "gauge stress-energy divergence identity plus sourced Maxwell route"
    )
    assert execution["target_rule"] == TARGET
    assert execution["theorem_target_statement"] == THEOREM_TARGET_STATEMENT
    assert execution["theorem_target_shape"]["given"] == ROUTE_GIVEN
    assert execution["theorem_target_shape"]["therefore"] == TARGET
    assert execution["route_steps"] == ROUTE_STEPS
    assert execution["accepted_gauge_stress_energy_divergence_identity"] == (
        ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
    )
    assert execution["accepted_sourced_maxwell_route"] == ACCEPTED_SOURCED_MAXWELL_ROUTE
    assert execution["gauge_stress_energy_divergence_identity_used"] is True
    assert execution["sourced_maxwell_route_used"] is True
    assert execution["same_F_and_J_objects_preserved"] is True
    assert execution["gauge_exchange_route_constructed"] is True
    assert execution["gauge_exchange_derived"] is True
    assert execution["plain_meaning"] == PLAIN_MEANING
    assert execution["watch_items"] == WATCH_ITEMS
    assert execution["lean_theorem_name"] == LEAN_THEOREM_NAME


def test_psi_A_gauge_exchange_attempt_execution_preserves_boundaries() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["proof_execution"] == "executed"
    assert execution["proof_execution_authorized"] is True
    assert execution["proof_attempt_executed"] is True
    assert execution["theorem_discharged"] is True
    assert execution["theorem_linkage_completed"] is True
    assert execution["theorem_linkage_obligation_discharged"] is True
    assert execution["rule_promoted"] is False
    assert execution["gap_1_through_gap_8_discharged"] is False
    assert execution["full_maxwell_closure_claimed"] is False
    assert execution["em_qft_closure_claimed"] is False
    assert execution["qft_gr_closure_claimed"] is False
    assert execution["gr_qm_closure_claimed"] is False
    assert execution["empirical_validation_claimed"] is False
    assert execution["seam_closure_claim"] is False
    assert execution["master_action_promoted"] is False


def test_psi_A_gauge_exchange_attempt_execution_records_lean_status() -> None:
    execution = _json(DEFAULT_OUT)

    assert execution["lean_status_wording"] == LEAN_STATUS_WORDING_FOR_EXECUTION
    assert (
        execution["full_toeformal_aggregate_status_for_execution"]
        == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
    )
    assert execution["scoped_lean_targets_status_for_execution"] == "PASSED_SERIAL_RERUN"
    assert execution["full_toeformal_aggregate_passed"] is False
    assert "full ToeFormal aggregate = PASSED_SERIAL_RERUN" not in json.dumps(execution)


def test_psi_A_gauge_exchange_attempt_execution_rotates_to_result_review() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, RESULT_REVIEW_TARGET)
    state = registry["current_target_state"]
    evidence = EXECUTION_LEAN_REL

    assert state["live_next_target"] == RESULT_REVIEW_TARGET
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["active_lane"] == RESULT_REVIEW_TARGET
    assert state["live_next_target_report"] == EXECUTION_REPORT_REL
    assert state["live_next_target_outcome"] == OUTCOME_ID

    executed = _workstream(CONSUMED_TARGET, registry)
    assert executed["status"] == "paused"
    assert executed["authorization_evidence"] == evidence
    assert executed["report"] == EXECUTION_REPORT_REL
    assert executed["execution_result"] == OUTCOME_ID
    assert executed["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert executed["proof_attempt_executed"] == "yes"
    assert executed["theorem_discharged"] == "yes"
    assert executed["selected_next_target"] == RESULT_REVIEW_TARGET

    active = _workstream(RESULT_REVIEW_TARGET, registry, status="active")
    assert active["authorization_evidence"] == evidence
    assert active["report"] == EXECUTION_REPORT_REL
    assert active["execution_result"] == OUTCOME_ID
    assert active["strict_execution_result"] == STRICT_EXECUTION_RESULT
    assert active["proof_attempt_executed"] == "yes"
    assert active["theorem_discharged"] == "yes"
    assert active["rule_promoted"] == "no"


def test_psi_A_gauge_exchange_attempt_execution_mirrors() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, RESULT_REVIEW_TARGET)

    for path in [CURRENT_SURFACES_PATH, ROADMAP_PATH]:
        text = _read(path)
        assert f"CURRENT_LIVE_NEXT_TARGET_v0: {RESULT_REVIEW_TARGET}" in text
        assert f"PREVIOUS_LIVE_NEXT_TARGET_v0: {CONSUMED_TARGET}" in text
        assert f"ACTIVE_LANE_v0: {RESULT_REVIEW_TARGET}" in text
        assert f"CURRENT_LIVE_TARGET_REPORT_v0: {EXECUTION_REPORT_REL}" in text
        assert f"CURRENT_LIVE_TARGET_OUTCOME_v0: {OUTCOME_ID}" in text

    lean = _read(LEAN_PACKET_PATH)
    assert LEAN_THEOREM_NAME in lean
    assert "divTA = gaugeLoss current" in lean
    assert "theoremLinkageObligationDischarged = true" in lean
    assert "masterActionPromoted = false" in lean

    assert (
        "import ToeFormal.Derivation.PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteExecution"
        in _read(AGGREGATE_LEAN)
    )
    assert (
        "PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteExecution.selectedNextTarget"
        in _read(CURRENT_TARGET_LEAN)
    )
    assert (
        "PsiAGaugeSectorExchangeTheoremLinkageAttemptFromSourcedMaxwellRouteExecution.executionResult"
        in _read(QFTGR_LEAN)
    )
    assert RESULT_REVIEW_TARGET in _read(CURRENT_AUTHORITY_LEAN)


def test_psi_A_gauge_exchange_attempt_execution_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_execution_gate.py"
    )
