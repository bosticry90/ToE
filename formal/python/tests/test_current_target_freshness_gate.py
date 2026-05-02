from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
GOVERNANCE_MANIFEST_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
)
CROSS_PILLAR_FRONTIER_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CrossPillarClosureFrontier.lean"
)
POST_SWEEP_QUEUE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "PostSweepTheoremQueue.lean"
)
QM_EVOLUTION_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QMEvolutionPostBudgetCrossPillarReview.lean"
)
EM_QFT_PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "EMQFTPhysicsBlockerProtocolRow.lean"
)
EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_SharedDynamicsResidualUnificationBridge.lean"
)

LIVE_TARGET = "derive_or_refute_em_qft_interface_alignment_semantic_bridge"
PREVIOUS_TARGET = "derive_or_refute_em_qft_shared_dynamics_residual_unification_bridge"
EXTRACTION_TARGET = "extract_em_qft_physics_blocker_into_protocol_row"
QM_REVIEW_TARGET = "qm_evolution_post_budget_cross_pillar_review"
STALE_SCALAR_ACTION = "derive_or_refute_evolution_to_transport_semantic_bridge"
SCALAR_PAUSED_ACTION = "paused_no_scalar_reopen_until_dependency_graph_change"
HISTORICAL_QUEUE_TOKEN = "HISTORICAL_NONLIVE_FIRST_WAVE_QUEUE_v0"
CURRENT_TARGET_TOKEN = f"CURRENT_LIVE_NEXT_TARGET_v0: {LIVE_TARGET}"
EM_QFT_PRIMARY_BLOCKER = "shared_dynamics_and_residual_unification"
EM_QFT_SECONDARY_BLOCKER = "interface_alignment_semantic_bridge"
EM_QFT_FRESH_DELTA_ID = (
    "EM_QFT_SHARED_DYNAMICS_RESIDUAL_UNIFICATION_BRIDGE_COUNTEREXAMPLE_FRESH_DELTA_v0"
)

PAUSED_LANES = {
    "scalar_qft_a2a15a1",
    "qm_stat_transport_residual",
    "qft_gr_source_map",
    "sr_covariance_cosmology_regime_transport",
    "qm_evolution_contract",
}
FORBIDDEN_ASSERTIONS = {
    "phase2_authorized",
    "seam_closure_claimed",
    "master_action_promoted",
    "empirical_claimed",
    "governance_manifest_enrollment_authorized",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def _control(payload: dict[str, Any], control_id: str) -> dict[str, Any]:
    for control in payload["controls"]:
        if control["control_id"] == control_id:
            return control
    raise AssertionError(f"Missing control: {control_id}")


def _workstream(payload: dict[str, Any], workstream_id: str) -> dict[str, Any]:
    for workstream in payload["workstreams"]:
        if workstream["workstream_id"] == workstream_id:
            return workstream
    raise AssertionError(f"Missing workstream: {workstream_id}")


def _iter_key_values(value: Any, path: tuple[str, ...] = ()) -> list[tuple[tuple[str, ...], Any]]:
    if isinstance(value, dict):
        pairs: list[tuple[tuple[str, ...], Any]] = []
        for key, child in value.items():
            pairs.extend(_iter_key_values(child, path + (str(key),)))
        return pairs
    if isinstance(value, list):
        pairs = []
        for index, child in enumerate(value):
            pairs.extend(_iter_key_values(child, path + (str(index),)))
        return pairs
    return [(path, value)]


def test_single_live_target_is_machine_pinned_after_qm_review() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["schema_id"] == "CURRENT_TARGET_STATE_v0"
    assert state["previous_live_next_target"] == PREVIOUS_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == str(
        EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert state["post_sweep_queue_authority_status"] == HISTORICAL_QUEUE_TOKEN
    assert set(state["paused_lanes"]) == PAUSED_LANES
    assert state["active_lane"] == "em_qft_physics_blocker_extraction"

    active_workstreams = [
        item for item in payload["workstreams"] if item.get("status") == "active"
    ]
    assert [item["workstream_id"] for item in active_workstreams] == [
        "em_qft_physics_blocker_extraction"
    ]
    assert active_workstreams[0]["authorized_next_strict_target"] == LIVE_TARGET
    assert active_workstreams[0]["consumed_target"] == PREVIOUS_TARGET
    assert active_workstreams[0]["prior_consumed_target"] == EXTRACTION_TARGET
    assert active_workstreams[0]["latest_surface"] == "EM_QFT_SHARED_DYNAMICS_RESIDUAL_UNIFICATION_BRIDGE_v0"
    assert active_workstreams[0]["last_fresh_delta_kind"] == "counterexample"
    assert active_workstreams[0]["last_fresh_delta_id"] == EM_QFT_FRESH_DELTA_ID
    assert active_workstreams[0]["primary_blocker"] == EM_QFT_PRIMARY_BLOCKER
    assert active_workstreams[0]["secondary_blocker"] == EM_QFT_SECONDARY_BLOCKER

    active_targets = {state["live_next_target"], active_workstreams[0]["authorized_next_strict_target"]}
    assert active_targets == {LIVE_TARGET}


def test_readme_registry_and_frontier_agree_on_live_target() -> None:
    payload = _registry()
    readme_text = _read(README_PATH)
    frontier_text = _read(CROSS_PILLAR_FRONTIER_PATH)
    review_text = _read(QM_EVOLUTION_REVIEW_PATH)
    protocol_text = _read(EM_QFT_PROTOCOL_ROW_PATH)
    shared_bridge_text = _read(EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH)

    assert CURRENT_TARGET_TOKEN in readme_text
    assert f'"live_next_target": "{LIVE_TARGET}"' in _read(REGISTRY_PATH)
    assert (
        'def currentLiveNextStrictTargetV0 : String :=\n'
        f'  "{LIVE_TARGET}"'
    ) in frontier_text
    assert (
        'def previousLiveNextStrictTargetV0 : String :=\n'
        f'  "{PREVIOUS_TARGET}"'
    ) in frontier_text
    assert (
        'def emQFTPhysicsBlockerExtractionTargetId : String :=\n'
        f'  "{EXTRACTION_TARGET}"'
    ) in review_text
    assert (
        'def emQFTSharedDynamicsResidualUnificationBridgeTargetId : String :=\n'
        f'  "{PREVIOUS_TARGET}"'
    ) in protocol_text
    assert (
        'def emQFTInterfaceAlignmentSemanticBridgeTargetId : String :=\n'
        f'  "{LIVE_TARGET}"'
    ) in shared_bridge_text
    assert payload["current_target_state"]["live_next_target"] == LIVE_TARGET


def test_no_stale_live_next_action_survives_in_registry() -> None:
    payload = _registry()
    scalar = _control(payload, "scalar_post_capstone_anti_loop")
    assert scalar["status"] == "paused"
    assert scalar["next_action"] == SCALAR_PAUSED_ACTION

    stale_live_paths: list[str] = []
    checked_key_suffixes = {"next_action", "next_strict_target", "next_action_after_retention"}
    for path, value in _iter_key_values(payload):
        if path and path[-1] in checked_key_suffixes and value == STALE_SCALAR_ACTION:
            stale_live_paths.append(".".join(path))
    assert not stale_live_paths, (
        "Completed bridge target still appears as a live next action: "
        + ", ".join(stale_live_paths)
    )

    qm_evolution = _workstream(payload, "qm_evolution_contract")
    assert qm_evolution["post_budget_review_status"] == "completed"
    assert qm_evolution["same_lane_continuation"] == "not_authorized"
    assert qm_evolution["next_strict_target"] == EXTRACTION_TARGET
    assert qm_evolution["next_action_after_retention"] == EXTRACTION_TARGET
    assert qm_evolution["stronger_qm_dynamics_bridge_derivation"] == "not_supplied"

    em_qft = _workstream(payload, "em_qft_physics_blocker_extraction")
    assert em_qft["status"] == "active"
    assert em_qft["authorized_next_strict_target"] == LIVE_TARGET
    assert em_qft["authorization_evidence"] == str(
        EM_QFT_PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert em_qft["last_fresh_delta_evidence"] == str(
        EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")


def test_paused_lanes_do_not_advertise_active_continuation() -> None:
    payload = _registry()

    for lane in PAUSED_LANES:
        workstream = _workstream(payload, lane)
        assert workstream["status"] == "paused", lane

        continuation_values = [
            value
            for key, value in workstream.items()
            if "continuation" in key or key.endswith("_reopen") or key == "same_lane_continuation"
        ]
        assert "authorized" not in continuation_values, lane

    assert _workstream(payload, "qm_evolution_contract")["scalar_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["qm_stat_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["qft_gr_reopen"] == "not_authorized"
    assert _workstream(payload, "qm_evolution_contract")["sr_cosmo_reopen"] == "not_authorized"


def test_historical_post_sweep_queue_cannot_override_live_target() -> None:
    payload = _registry()
    queue_text = _read(POST_SWEEP_QUEUE_PATH)

    assert HISTORICAL_QUEUE_TOKEN in queue_text
    assert "live_next_target_source := False" in queue_text
    assert (
        _control(payload, "post_sweep_queue_discipline")["authority_status"]
        == HISTORICAL_QUEUE_TOKEN
    )
    assert _control(payload, "post_sweep_queue_discipline")["live_next_target_authority"] is False

    historical_targets = set(re.findall(r'target\s*:=\s*"([^"]+)"', queue_text))
    assert historical_targets
    assert LIVE_TARGET not in historical_targets
    assert PREVIOUS_TARGET not in historical_targets
    assert EXTRACTION_TARGET not in historical_targets
    assert QM_REVIEW_TARGET not in historical_targets


def test_forbidden_promotion_boundaries_remain_fail_closed() -> None:
    payload = _registry()
    assertions = payload["non_promotion_assertions"]
    assert set(assertions) == FORBIDDEN_ASSERTIONS
    assert not any(assertions.values())

    state = payload["current_target_state"]
    assert set(state["forbidden_promotions"]) == {
        "phase2_authorization",
        "seam_closure",
        "empirical_claim",
        "master_action_promotion",
        "governance_manifest_enrollment",
    }

    protocol_text = _read(EM_QFT_PROTOCOL_ROW_PATH)
    shared_bridge_text = _read(EM_QFT_SHARED_DYNAMICS_BRIDGE_PATH)
    for theorem_name in [
        "em_qft_protocol_row_phase2_not_authorized_v0",
        "em_qft_protocol_row_seam_not_closed_v0",
        "em_qft_protocol_row_master_action_not_promoted_v0",
        "em_qft_protocol_row_no_empirical_claim_v0",
        "em_qft_protocol_row_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in protocol_text
    for theorem_name in [
        "em_qft_shared_dynamics_phase2_not_authorized_v0",
        "em_qft_shared_dynamics_no_seam_closure_v0",
        "em_qft_shared_dynamics_master_action_not_promoted_v0",
        "em_qft_shared_dynamics_no_empirical_claim_v0",
        "em_qft_shared_dynamics_governance_manifest_not_enrolled_v0",
    ]:
        assert theorem_name in shared_bridge_text


def test_current_target_gate_is_not_governance_manifest_enrolled() -> None:
    manifest_text = _read(GOVERNANCE_MANIFEST_PATH)
    assert "test_current_target_freshness_gate.py" not in manifest_text
