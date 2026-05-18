from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_20260515_v0"
SELECTION_ID = "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_v0"
OUTCOME_ID = "MAIN_PHYSICS_TARGET_SELECTION_RESUMED_AFTER_COMPUTATIONAL_PHYSICS_NONCLAIM_STACK_CLOSEOUT"
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_CLOSEOUT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_LOOP_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
DEFAULT_V01_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_20260513_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_20260515_v0.json"
)

EXPECTED_CONSUMED_REVIEW = "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_v0"
EXPECTED_CLOSED_STATUS = "CLOSED_BOUNDED_NONCLAIM"
EXPECTED_RETURN_ACTION = "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
EXPECTED_LIVE_SELECTOR = "select_next_post_v01_alpha_manifest_enrollment_bounded_attack"
EXPECTED_LIVE_SELECTOR_LANE = "v01_alpha_governance_manifest_enrollment_result_review"
EXPECTED_SELECTED_TARGET = "prepare_v01_alpha_release_packet_gap_review"

COMPUTATIONAL_STACK_MARKERS = [
    "COMPUTATIONAL_PHYSICS",
    "VVUQ",
    "NUMERICAL_METHOD_VERIFICATION",
    "REGIME_RECOVERY",
    "SENSITIVITY_ROBUSTNESS",
    "REFERENT_REGISTRY",
    "SIMULATION_MODEL_CARD",
    "PREDICTION_AND_FALSIFIER",
]

FORBIDDEN_EFFECTS = [
    "computational_physics_execution_surface_opened",
    "theory_validation_authorized",
    "empirical_validation_authorized",
    "referent_comparison_execution_authorized",
    "robustness_scan_execution_authorized",
    "prediction_execution_authorized",
    "falsifier_execution_authorized",
    "theorem_discharge_authorized",
    "blocker_movement_authorized",
    "lane_reopen_authorized",
    "seam_closure_authorized",
    "phase2_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "release_packet_assembly_authorized",
    "public_release_completion_authorized",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _find_workstream(loop_registry: dict[str, Any], workstream_id: str) -> dict[str, Any]:
    for row in loop_registry.get("workstreams", []):
        if row.get("workstream_id") == workstream_id:
            return row
    return {}


def _target_outside_computational_stack(target: str) -> bool:
    upper_target = target.upper()
    return all(marker not in upper_target for marker in COMPUTATIONAL_STACK_MARKERS)


def _candidate_targets(v01_review: dict[str, Any], selected_target: str) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for row in v01_review.get("candidate_selector_targets", []):
        target = str(row.get("target", ""))
        recommendation = str(row.get("recommendation", ""))
        rows.append(
            {
                "target": target,
                "source_recommendation": recommendation,
                "decision": "selected" if target == selected_target else "deferred",
                "reason": str(row.get("reason", "")),
            }
        )
    return rows


def build_selection(
    *,
    closeout_review_path: Path = DEFAULT_CLOSEOUT_REVIEW_PATH,
    loop_registry_path: Path = DEFAULT_LOOP_REGISTRY_PATH,
    v01_review_path: Path = DEFAULT_V01_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout_review = _read_json(closeout_review_path)
    loop_registry = _read_json(loop_registry_path)
    v01_review = _read_json(v01_review_path)
    current_target_state = loop_registry.get("current_target_state", {})
    workstream = _find_workstream(loop_registry, EXPECTED_LIVE_SELECTOR_LANE)
    selected_target = str(v01_review.get("recommended_selector_choice", ""))
    candidate_targets = _candidate_targets(v01_review, selected_target)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    selected_outside_stack = _target_outside_computational_stack(selected_target)
    selected_count = sum(1 for row in candidate_targets if row["decision"] == "selected")
    target_coverage = set(loop_registry.get("next_strict_target_coverage", []))
    expected_selector_recorded = (
        current_target_state.get("live_next_target") == EXPECTED_LIVE_SELECTOR
        or EXPECTED_LIVE_SELECTOR in target_coverage
    )
    expected_lane_recorded = (
        current_target_state.get("active_lane") == EXPECTED_LIVE_SELECTOR_LANE
        or workstream.get("workstream_id") == EXPECTED_LIVE_SELECTOR_LANE
    )

    acceptance_criteria = {
        "consumes_closeout_result_review": closeout_review.get("review_id") == EXPECTED_CONSUMED_REVIEW,
        "closeout_result_review_accepted": closeout_review.get("accepted") is True,
        "computational_physics_stack_closed": closeout_review.get("roadmap_terminal_status")
        == EXPECTED_CLOSED_STATUS,
        "closeout_review_returns_to_main_selection": closeout_review.get("next_action") == EXPECTED_RETURN_ACTION,
        "loop_registry_live_selector_matches": expected_selector_recorded,
        "loop_registry_active_lane_matches": expected_lane_recorded,
        "workstream_recommends_gap_review": workstream.get("recommended_selector_choice")
        == EXPECTED_SELECTED_TARGET,
        "v01_review_recommends_gap_review": selected_target == EXPECTED_SELECTED_TARGET,
        "v01_review_selector_choice_unexecuted": v01_review.get("review_executes_selector_choice") is False,
        "exactly_one_main_target_selected": selected_count == 1,
        "selected_target_outside_computational_physics_stack": selected_outside_stack,
        "selected_target_not_release_assembly": selected_target != "assemble_v01_alpha_public_release_packet",
        "computational_physics_execution_surface_closed": forbidden_effect_status[
            "computational_physics_execution_surface_opened"
        ]
        is False,
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "selection_id": SELECTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "outcome_id": OUTCOME_ID if accepted else "MAIN_PHYSICS_TARGET_SELECTION_BLOCKED_AFTER_CLOSEOUT",
        "accepted": accepted,
        "consumes_result_review": EXPECTED_CONSUMED_REVIEW,
        "consumes_result_review_pointer": _ptr(closeout_review_path),
        "source_loop_registry": "LOOP_CONTROL_REGISTRY_v0",
        "source_loop_registry_pointer": _ptr(loop_registry_path),
        "source_selector_review": "V01_ALPHA_GOVERNANCE_MANIFEST_ENROLLMENT_RESULT_REVIEW_v0",
        "source_selector_review_pointer": _ptr(v01_review_path),
        "computational_physics_stack_status": EXPECTED_CLOSED_STATUS,
        "selection_status": "selected_one_main_target_nonclaim" if accepted else "blocked",
        "selected_target": selected_target,
        "selected_target_kind": "main_release_gap_review_preparation_only",
        "selected_target_source": _ptr(v01_review_path),
        "selected_target_outside_computational_physics_stack": selected_outside_stack,
        "selection_count": selected_count,
        "candidate_target_count": len(candidate_targets),
        "candidate_targets": candidate_targets,
        "selection_executes_target": False,
        "selected_target_execution_status": "not_executed_by_this_packet",
        "next_action": selected_target if accepted else "REMEDIATE_MAIN_PHYSICS_TARGET_SELECTION_AFTER_CLOSEOUT",
        "next_action_scope": "MAIN_PROJECT_TARGET_PREPARATION_ONLY_NO_COMPUTATIONAL_PHYSICS_EXECUTION",
        "current_repo_live_target_readout": {
            "loop_registry_live_next_target": (
                EXPECTED_LIVE_SELECTOR
                if expected_selector_recorded
                else current_target_state.get("live_next_target")
            ),
            "loop_registry_active_lane": (
                EXPECTED_LIVE_SELECTOR_LANE
                if expected_lane_recorded
                else current_target_state.get("active_lane")
            ),
            "selector_review_selected_next_target": v01_review.get("selected_next_target"),
            "selector_review_recommended_choice": v01_review.get("recommended_selector_choice"),
            "selector_choice_executed": v01_review.get("review_executes_selector_choice"),
            "workstream_selected_next_target": workstream.get("selected_next_target"),
            "workstream_recommended_selector_choice": workstream.get("recommended_selector_choice"),
            "workstream_selector_choice_executed": workstream.get("selector_choice_executed"),
        },
        "gap_review_required_checks": v01_review.get("gap_review_required_checks", []),
        "forbidden_effect_status": forbidden_effect_status,
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "Main physics target selection after computational-physics closeout is a routing packet only. It "
            "consumes the closed nonclaim computational-physics stack, opens no computational-physics execution "
            "surface, and selects one main governance target for later preparation. It does not authorize theory "
            "validation, empirical validation, referent comparison execution, robustness scan execution, prediction "
            "execution, falsifier execution, theorem discharge, blocker movement, lane reopen, seam closure, Phase 2 "
            "authorization, release packet assembly, public release completion, master-action promotion, claim "
            "promotion, or external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_selection(
    *,
    closeout_review_path: Path = DEFAULT_CLOSEOUT_REVIEW_PATH,
    loop_registry_path: Path = DEFAULT_LOOP_REGISTRY_PATH,
    v01_review_path: Path = DEFAULT_V01_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_selection(
        closeout_review_path=closeout_review_path,
        loop_registry_path=loop_registry_path,
        v01_review_path=v01_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the main physics target selection after computational-physics closeout."
    )
    parser.add_argument("--closeout-review", type=Path, default=DEFAULT_CLOSEOUT_REVIEW_PATH)
    parser.add_argument("--loop-registry", type=Path, default=DEFAULT_LOOP_REGISTRY_PATH)
    parser.add_argument("--v01-review", type=Path, default=DEFAULT_V01_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    closeout_review_path = (
        ns.closeout_review if ns.closeout_review.is_absolute() else (REPO_ROOT / ns.closeout_review)
    )
    loop_registry_path = ns.loop_registry if ns.loop_registry.is_absolute() else (REPO_ROOT / ns.loop_registry)
    v01_review_path = ns.v01_review if ns.v01_review.is_absolute() else (REPO_ROOT / ns.v01_review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_selection(
        closeout_review_path=closeout_review_path,
        loop_registry_path=loop_registry_path,
        v01_review_path=v01_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "main_physics_target_selection_after_computational_physics_closeout_report: "
        f"accepted={payload['accepted']} selected_target={payload['selected_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
