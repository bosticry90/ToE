from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
BRIDGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "EM_QFT_InterfaceAlignmentSemanticBridge.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
GOVERNANCE_MANIFEST_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)

CONSUMED_TARGET = "derive_or_refute_em_qft_interface_alignment_semantic_bridge"
LIVE_TARGET = "em_qft_post_budget_cross_pillar_review"
SURFACE_ID = "EM_QFT_INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_v0"
FRESH_DELTA_ID = "EM_QFT_INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_COUNTEREXAMPLE_FRESH_DELTA_v0"
RETAINED_BLOCKER = "PHASE1-BLOCKER-EMQFT-INTERFACE-ALIGNMENT-SEMANTIC-BRIDGE-RETAINED"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict:
    return json.loads(_read(REGISTRY_PATH))


def test_interface_alignment_bridge_surface_records_counterexample_and_package_route() -> None:
    text = _read(BRIDGE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        LIVE_TARGET,
        FRESH_DELTA_ID,
        RETAINED_BLOCKER,
        "counterexample",
        "EMQFTInterfaceAlignmentPackage",
        "supplied_interface_alignment_semantics_construct_bridge_package_v0",
        "interface_alignment_package_does_not_force_source_current_semantics_v0",
        "interface_alignment_package_does_not_force_gauge_quantization_semantics_v0",
        "em_qft_interface_alignment_attempt_budget_reached_v0",
        "em_qft_interface_alignment_same_lane_not_authorized_v0",
        "em_qft_interface_alignment_selected_next_target_v0",
    }:
        assert token in text


def test_interface_alignment_bridge_preserves_nonpromotion_boundaries() -> None:
    text = _read(BRIDGE_PATH)

    for token in {
        "em_qft_seam_closed := False",
        "phase2Authorized := False",
        "master_action_promoted := False",
        "empirical_claim := False",
        "governance_manifest_enrollment_authorized := False",
        "em_qft_interface_alignment_no_seam_closure_v0",
        "em_qft_interface_alignment_phase2_not_authorized_v0",
        "em_qft_interface_alignment_master_action_not_promoted_v0",
        "em_qft_interface_alignment_no_empirical_claim_v0",
        "em_qft_interface_alignment_governance_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_frontier_and_aggregate_rotate_to_em_qft_post_budget_review() -> None:
    aggregate_text = _read(AGGREGATE_PATH)
    frontier_text = _read(FRONTIER_PATH)

    assert "import ToeFormal.Bridges.EM_QFT_InterfaceAlignmentSemanticBridge" in aggregate_text
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{CONSUMED_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text
    assert RETAINED_BLOCKER in frontier_text


def test_registry_tracks_interface_alignment_slice_and_attempt_budget() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == str(
        BRIDGE_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")

    assert RETAINED_BLOCKER in payload["retained_blocker_coverage"]
    assert CONSUMED_TARGET in payload["next_strict_target_coverage"]
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["em_qft_physics_blocker_extraction"]
    workstream = active[0]
    assert workstream["retained_blocker"] == RETAINED_BLOCKER
    assert workstream["consumed_target"] == CONSUMED_TARGET
    assert workstream["authorized_next_strict_target"] == LIVE_TARGET
    assert workstream["latest_surface"] == SURFACE_ID
    assert workstream["last_fresh_delta_kind"] == "counterexample"
    assert workstream["last_fresh_delta_id"] == FRESH_DELTA_ID
    assert workstream["interface_alignment_only_source_current_closure"] == "refuted"
    assert workstream["interface_alignment_only_gauge_quantization_closure"] == "refuted"
    assert workstream["attempt_budget_status"] == "two_consecutive_retained_slices_reached_post_budget_review_required"
    assert workstream["same_lane_continuation"] == "not_authorized_attempt_budget_reached"
    assert workstream["post_budget_review_status"] == "pending"


def test_docs_expose_post_budget_target_without_manifest_enrollment() -> None:
    for path in [
        README_PATH,
        STATE_PATH,
        ROADMAP_PATH,
        STRICT_MAP_PATH,
        SEAM_REGISTRY_PATH,
        SEAM_INVENTORY_PATH,
    ]:
        text = _read(path)
        assert LIVE_TARGET in text, f"{path} missing live target"

    assert SURFACE_ID in _read(STATE_PATH)
    assert SURFACE_ID in _read(STRICT_MAP_PATH)
    assert "SEAM_EM_QFT_INTERFACE_ALIGNMENT_STATUS_v0" in _read(SEAM_REGISTRY_PATH)
    assert "test_em_qft_interface_alignment_semantic_bridge_gate.py" not in _read(
        GOVERNANCE_MANIFEST_PATH
    )
