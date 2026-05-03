from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
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
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
GOVERNANCE_MANIFEST_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
)
CROSS_PILLAR_FRONTIER_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CrossPillarClosureFrontier.lean"
)

PUBLIC_CURRENT_TARGET_SURFACES = (
    README_PATH,
    STATE_PATH,
    ROADMAP_PATH,
    STRICT_MAP_PATH,
)


def repo_root() -> Path:
    return REPO_ROOT


def read_text(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(read_text(path))


def loop_registry() -> dict[str, Any]:
    return read_json(REGISTRY_PATH)


def current_target_state(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    registry = payload if payload is not None else loop_registry()
    return registry["current_target_state"]


def active_workstream(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    registry = payload if payload is not None else loop_registry()
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    assert len(active) == 1, f"Expected one active workstream, found {len(active)}"
    return active[0]


def workstream(workstream_id: str, payload: dict[str, Any] | None = None) -> dict[str, Any]:
    registry = payload if payload is not None else loop_registry()
    for item in registry["workstreams"]:
        if item["workstream_id"] == workstream_id:
            return item
    raise AssertionError(f"Missing workstream: {workstream_id}")


def assert_current_target_consistent() -> None:
    payload = loop_registry()
    state = current_target_state(payload)
    active = active_workstream(payload)

    live_target = state["live_next_target"]
    evidence_path = REPO_ROOT / state["live_next_target_evidence"]
    assert state["schema_id"] == "CURRENT_TARGET_STATE_v0"
    assert evidence_path.exists(), f"Missing live target evidence: {evidence_path}"
    assert active["workstream_id"] == state["active_lane"]
    assert active["authorized_next_strict_target"] == live_target

    for lane in state["paused_lanes"]:
        paused = next(
            (item for item in payload["workstreams"] if item["workstream_id"] == lane),
            None,
        )
        assert paused is not None, f"Paused lane missing from workstreams: {lane}"
        assert paused["status"] == "paused", f"Paused lane is not paused: {lane}"

    assert live_target in payload["next_strict_target_coverage"]


def assert_frontier_matches_registry() -> None:
    state = current_target_state()
    frontier_text = read_text(CROSS_PILLAR_FRONTIER_PATH)
    previous_target = state["previous_live_next_target"]
    live_target = state["live_next_target"]

    assert (
        f'def previousLiveNextStrictTargetV0 : String :=\n  "{previous_target}"'
        in frontier_text
    )
    assert (
        f'def currentLiveNextStrictTargetV0 : String :=\n  "{live_target}"'
        in frontier_text
    )
    assert (
        f'next_strict_slice := "{live_target}"' in frontier_text
        or f'next_strict_slice :=\n        "{live_target}"' in frontier_text
    )


def assert_public_surfaces_match_registry(
    paths: tuple[Path, ...] = PUBLIC_CURRENT_TARGET_SURFACES,
) -> None:
    live_target = current_target_state()["live_next_target"]
    for path in paths:
        assert live_target in read_text(path), f"{path} missing live target"


def assert_forbidden_promotions_closed() -> None:
    payload = loop_registry()
    assertions = payload["non_promotion_assertions"]
    assert assertions == {
        "phase2_authorized": False,
        "seam_closure_claimed": False,
        "master_action_promoted": False,
        "empirical_claimed": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert set(current_target_state(payload)["forbidden_promotions"]) == {
        "phase2_authorization",
        "seam_closure",
        "empirical_claim",
        "master_action_promotion",
        "governance_manifest_enrollment",
    }


def assert_focused_gate_not_manifest_enrolled(test_filename: str) -> None:
    assert test_filename not in read_text(GOVERNANCE_MANIFEST_PATH)
