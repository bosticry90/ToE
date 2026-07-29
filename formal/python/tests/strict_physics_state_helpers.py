from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

import pytest

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
CURRENT_AUTHORITATIVE_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
CROSS_PILLAR_FRONTIER_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CrossPillarClosureFrontier.lean"
)

PUBLIC_CURRENT_TARGET_SURFACES = (
    README_PATH,
    STATE_PATH,
    ROADMAP_PATH,
    STRICT_MAP_PATH,
    CURRENT_AUTHORITATIVE_SURFACES_PATH,
)

STRICT_CURRENT_TOKEN_SURFACES = (
    README_PATH,
    STATE_PATH,
    ROADMAP_PATH,
    STRICT_MAP_PATH,
)

LATEST_CURRENT_BLOCK_MARKERS = {
    README_PATH: (
        "CURRENT SCIENTIFIC CHECKPOINT (2026-07-29)",
        "CURRENT-MAINTENANCE NOTE",
    ),
    STATE_PATH: (
        "## CURRENT SCIENTIFIC CHECKPOINT (2026-07-29)",
        "## AUTHORITY_SURFACE_v2",
    ),
    ROADMAP_PATH: (
        "Current native-hypothesis frontier (2026-07-29):",
        "POST_MR_MATURATION_EXECUTION_STATUS_v0:",
    ),
    STRICT_MAP_PATH: (
        "Current strict native-hypothesis obligation (2026-07-29):",
        "POST_MR_MATURATION_EXECUTION_STATUS_v0:",
    ),
}


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


def assert_historical_target_recorded(
    *,
    payload: dict[str, Any],
    previous_target: str | None = None,
    live_target: str | None = None,
    evidence: str | None = None,
    lane: str | None = None,
) -> bool:
    """Validate an old live-target transition without requiring it to be current.

    Historical focused gates should continue to protect their packet/workstream
    rows after the single global live target has advanced. The return value is
    true only when the checked transition is still the current live transition.
    """
    state = current_target_state(payload)
    is_current = True

    if previous_target is not None:
        is_current = is_current and state["previous_live_next_target"] == previous_target
    if live_target is not None:
        is_current = is_current and state["live_next_target"] == live_target
    if evidence is not None:
        is_current = is_current and state["live_next_target_evidence"] == evidence
    if lane is not None:
        is_current = is_current and state["active_lane"] == lane

    if is_current:
        return True

    coverage = set(payload["next_strict_target_coverage"])
    if previous_target is not None:
        assert previous_target in coverage
    if live_target is not None:
        assert live_target in coverage
    if evidence is not None:
        evidence_path = REPO_ROOT / evidence
        assert evidence_path.exists(), f"Missing historical target evidence: {evidence_path}"
    if lane is not None:
        ids = {item["workstream_id"] for item in payload["workstreams"]}
        assert lane in ids or lane in state["paused_lanes"]
    return False


def skip_if_not_current_target(payload: dict[str, Any], expected_live_target: str) -> None:
    state = current_target_state(payload)
    live_target = state["live_next_target"]
    if live_target != expected_live_target:
        assert expected_live_target in payload["next_strict_target_coverage"]
        pytest.skip(
            "historical live-target transition; current live target is "
            f"{live_target!r}, not {expected_live_target!r}"
        )


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
    assert (
        "def masterActionFrontierNextStrictTargetV0 : String :=\n"
        '  "close_toe_native_surrogate_v0_after_bounded_result_v0"'
        in frontier_text
    )
    assert (
        "next_strict_slice :=\n"
        "        masterActionFrontierNextStrictTargetV0"
        in frontier_text
    )


def assert_public_surfaces_match_registry(
    paths: tuple[Path, ...] = PUBLIC_CURRENT_TARGET_SURFACES,
) -> None:
    state = current_target_state()
    live_target = state["live_next_target"]
    expected_tokens = {
        "CURRENT_LIVE_NEXT_TARGET_v0": live_target,
        "PREVIOUS_LIVE_NEXT_TARGET_v0": state["previous_live_next_target"],
        "ACTIVE_LANE_v0": state["active_lane"],
        "CURRENT_LIVE_TARGET_AUTHORITY_v0": str(
            REGISTRY_PATH.relative_to(REPO_ROOT)
        ).replace("\\", "/"),
        "CURRENT_LIVE_TARGET_FRONTIER_MIRROR_v0": state[
            "live_next_target_frontier_source"
        ],
        "CURRENT_LIVE_TARGET_EVIDENCE_v0": state["live_next_target_evidence"],
        "CURRENT_LIVE_TARGET_REPORT_v0": state["live_next_target_report"],
        "CURRENT_LIVE_TARGET_OUTCOME_v0": state["live_next_target_outcome"],
    }
    for path in paths:
        text = read_text(path)
        assert live_target in text, f"{path} missing live target"
        text_to_check = text
        if path == CURRENT_AUTHORITATIVE_SURFACES_PATH:
            marker = "Current live control state:"
            assert marker in text, f"{path} missing {marker}"
            text_to_check = text.split(marker, 1)[1].split("\n\n", 1)[0]
        elif path in STRICT_CURRENT_TOKEN_SURFACES:
            start_marker, end_marker = LATEST_CURRENT_BLOCK_MARKERS[path]
            assert start_marker in text, f"{path} missing {start_marker}"
            assert end_marker in text, f"{path} missing {end_marker}"
            text_to_check = text.split(start_marker, 1)[1].split(end_marker, 1)[0]

        for label, value in expected_tokens.items():
            pattern = rf"(?m)^(?:- `)?{re.escape(label)}:\s*([^`\r\n]+)`?\s*$"
            matches = [match.strip() for match in re.findall(pattern, text_to_check)]
            assert matches, f"{path} missing {label}: {value}"
            if path in STRICT_CURRENT_TOKEN_SURFACES:
                assert all(match == value for match in matches), (
                    f"{path} has stale {label}: {matches}; expected {value}"
                )
            else:
                assert value in matches, f"{path} missing {label}: {value}"

        current_citation_targets = re.findall(
            r"MASTER_ACTION_CURRENT_CITATION_TARGET_v0:\s*([A-Za-z0-9_]+)",
            text_to_check,
        )
        assert all(
            target == live_target for target in current_citation_targets
        ), f"{path} has stale master-action current citation target"


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
