from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROTOCOL_ROW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "EMQFTPhysicsBlockerProtocolRow.lean"
)
CROSS_PILLAR_FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
DERIVATION_DIR = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
GOVERNANCE_MANIFEST_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)

CONSUMED_TARGET = "extract_em_qft_physics_blocker_into_protocol_row"
LIVE_TARGET = "derive_or_refute_em_qft_shared_dynamics_residual_unification_bridge"
PRIMARY_BLOCKER = "shared_dynamics_and_residual_unification"
SECONDARY_BLOCKER = "interface_alignment_semantic_bridge"
REQUIRED_EVIDENCE = {
    "EM_QFT_INTERFACE_ALIGNMENT_BRIDGE_OBLIGATION_v0",
    "EM_QFT_SHARED_DYNAMICS_WITNESS_REQUIRED_v0",
    "EM_QFT_RESIDUAL_UNIFICATION_SEMANTIC_BRIDGE_REQUIRED_v0",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict:
    return json.loads(_read(REGISTRY_PATH))


def test_em_qft_protocol_row_records_blocker_without_promotion() -> None:
    text = _read(PROTOCOL_ROW_PATH)

    for token in {
        "em_qft_physics_blocker_protocol_row_v0",
        "SEAM-EM-QFT",
        CONSUMED_TARGET,
        LIVE_TARGET,
        PRIMARY_BLOCKER,
        SECONDARY_BLOCKER,
        "theorem_linked_shared_dynamics_discharge",
        "theorem_linked_residual_unification_discharge",
        "theorem_linked_interface_alignment_discharge",
        "em_qft_protocol_row_physics_incomplete_v0",
        "em_qft_protocol_row_seam_not_closed_v0",
        "em_qft_protocol_row_phase2_not_authorized_v0",
        "em_qft_protocol_row_master_action_not_promoted_v0",
        "em_qft_protocol_row_no_empirical_claim_v0",
        "em_qft_protocol_row_governance_manifest_not_enrolled_v0",
    } | REQUIRED_EVIDENCE:
        assert token in text

    assert "physics_complete := False" in text
    assert "em_qft_seam_closed := False" in text
    assert "phase2Authorized := False" in text
    assert "master_action_promoted := False" in text
    assert "empirical_claim := False" in text
    assert "governance_manifest_enrollment_authorized := False" in text


def test_frontier_uses_row_lookup_and_exposes_successor_target() -> None:
    frontier_text = _read(CROSS_PILLAR_FRONTIER_PATH)

    assert "def crossPillarFrontierEntryByRow?" in frontier_text
    assert f'def previousLiveNextStrictTargetV0 : String :=\n  "{CONSUMED_TARGET}"' in frontier_text
    assert f'def currentLiveNextStrictTargetV0 : String :=\n  "{LIVE_TARGET}"' in frontier_text
    assert f'next_strict_slice :=\n        "{LIVE_TARGET}"' in frontier_text

    review_files = [
        DERIVATION_DIR / "QMEvolutionPostBudgetCrossPillarReview.lean",
        DERIVATION_DIR / "QFTGRPostBudgetCrossPillarReview.lean",
        DERIVATION_DIR / "SRCosmologyPostBudgetCrossPillarReview.lean",
    ]
    for path in review_files:
        text = _read(path)
        assert "crossPillarFrontierEntryByRow?" in text
        assert "crossPillarClosureFrontierV0.drop" not in text


def test_loop_registry_and_public_surfaces_follow_em_qft_successor() -> None:
    payload = _registry()
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == LIVE_TARGET
    assert state["live_next_target_evidence"] == str(
        PROTOCOL_ROW_PATH.relative_to(REPO_ROOT)
    ).replace("\\", "/")
    assert LIVE_TARGET in payload["next_strict_target_coverage"]

    active = [item for item in payload["workstreams"] if item.get("status") == "active"]
    assert [item["workstream_id"] for item in active] == ["em_qft_physics_blocker_extraction"]
    assert active[0]["consumed_target"] == CONSUMED_TARGET
    assert active[0]["authorized_next_strict_target"] == LIVE_TARGET
    assert active[0]["primary_blocker"] == PRIMARY_BLOCKER
    assert active[0]["secondary_blocker"] == SECONDARY_BLOCKER
    assert set(active[0]["required_evidence"]) == REQUIRED_EVIDENCE

    edges = {(edge["from"], edge["to"]) for edge in payload["dependency_edges"]}
    assert (
        "em_qft_physics_blocker_extraction",
        "em_qft_shared_dynamics_residual_unification_bridge",
    ) in edges

    for path in [REPO_ROOT / "README.md", REPO_ROOT / "State_of_the_Theory.md"]:
        assert f"CURRENT_LIVE_NEXT_TARGET_v0: {LIVE_TARGET}" in _read(path)


def test_em_qft_seam_registry_names_blocker_and_boundary() -> None:
    for path in [SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH]:
        text = _read(path)
        assert "SEAM_EM_QFT_GOVERNANCE_COMPLETE_v0: YES" in text
        assert "SEAM_EM_QFT_PHYSICS_COMPLETE_v0: NO" in text
        assert "SEAM_EM_QFT_PHYSICS_BLOCKER_v0: SHARED_DYNAMICS_AND_RESIDUAL_UNIFICATION_NOT_DISCHARGED" in text
        assert "SEAM_EM_QFT_SECONDARY_PHYSICS_BLOCKER_v0: INTERFACE_ALIGNMENT_SEMANTIC_BRIDGE_NOT_DISCHARGED" in text
        assert f"SEAM_EM_QFT_CURRENT_PHYSICS_BLOCKER_TARGET_v0: {LIVE_TARGET}" in text
        assert "NO_EM_QFT_SEAM_CLOSURE_NO_MASTER_ACTION_PROMOTION" in text


def test_em_qft_protocol_gate_is_focused_not_manifest_enrolled() -> None:
    manifest_text = _read(GOVERNANCE_MANIFEST_PATH)
    assert "test_em_qft_physics_blocker_protocol_row_gate.py" not in manifest_text
