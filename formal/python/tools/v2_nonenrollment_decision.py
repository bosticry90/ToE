from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.loop_control_registry_integrity import (
    DEFAULT_REGISTRY_PATH,
    atomic_write_registry,
    canonical_json_bytes,
    load_registry,
    repair_registry,
    validate_registry,
)


REPO_ROOT = find_repo_root(Path(__file__))
DECISION_RELATIVE_PATH = (
    "formal/docs/release/V2_ENROLLMENT_DECISION_20260725_v0.json"
)
DECISION_PATH = REPO_ROOT / DECISION_RELATIVE_PATH
DECISION_SHA256 = "5f294a4c28902b11ba8ad6e0fc82866205298cb65c468691a3aaaaf43e4b5f63"

PRIOR_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)
WAITING_TARGET = "await_fresh_response_selector_after_v2_nonenrollment_v0"
WAITING_KIND = "nonexecuting_scientific_target_selection_boundary"
WAITING_OUTCOME = (
    "V2_REPRODUCIBLE_BUT_NOT_ENROLLED_PREPARATION_TARGET_"
    "CLOSED_WITHOUT_ACCEPTANCE"
)
WAITING_STRICT_OUTCOME = (
    "B_BLOCKED_NO_V2_ENROLLMENT_NO_EXECUTABLE_SCIENTIFIC_TARGET_"
    "FRESH_RESPONSE_SELECTOR_REQUIRED_NO_SCIENTIFIC_EXECUTION"
)


class V2NonEnrollmentDecisionError(ValueError):
    pass


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _workstream(registry: dict[str, Any], target: str) -> dict[str, Any]:
    rows = [
        row
        for row in registry.get("workstreams", [])
        if isinstance(row, dict) and row.get("workstream_id") == target
    ]
    if len(rows) != 1:
        raise V2NonEnrollmentDecisionError(
            f"expected one workstream for {target!r}, found {len(rows)}"
        )
    return rows[0]


def transition_registry(registry: dict[str, Any]) -> dict[str, Any]:
    if sha256_path(DECISION_PATH) != DECISION_SHA256:
        raise V2NonEnrollmentDecisionError("V2 decision record identity drift")

    state = registry.get("current_target_state")
    if not isinstance(state, dict):
        raise V2NonEnrollmentDecisionError("current_target_state is missing")
    live_target = state.get("live_next_target")
    if live_target not in {PRIOR_TARGET, WAITING_TARGET}:
        raise V2NonEnrollmentDecisionError(
            "V2 non-enrollment transition has already executed or the parent "
            "scientific target is not the accepted preparation target"
        )

    prior = _workstream(registry, PRIOR_TARGET)
    waiting_row_contract = {
        "workstream_id": WAITING_TARGET,
        "status": "active",
        "live_lane": "yes",
        "queue_scope": (
            "nonexecuting boundary awaiting one fresh response selector after "
            "explicit V2 non-enrollment"
        ),
        "active_lane": WAITING_TARGET,
        "authorized_target": WAITING_TARGET,
        "authorized_next_strict_target": WAITING_TARGET,
        "selected_next_target": WAITING_TARGET,
        "selected_next_target_kind": WAITING_KIND,
        "authorization_evidence": DECISION_RELATIVE_PATH,
        "report": DECISION_RELATIVE_PATH,
        "report_path": DECISION_RELATIVE_PATH,
        "report_sha256": DECISION_SHA256,
        "packet_result": WAITING_OUTCOME,
        "strict_packet_result": WAITING_STRICT_OUTCOME,
        "consumed_target": PRIOR_TARGET,
        "consumed_target_kind": (
            "pillar_seam_unit_mapping_ledger_blocker_response_"
            "route_selection_packet_v2"
        ),
        "claim_ceiling_level": 3,
        "claim_label": "B-BLOCKED",
        "claim_status": "recovery_complete_v2_reproducible_not_enrolled",
        "review_accepted": "yes",
        "v2_reproducible": "yes",
        "v2_enrolled": "no",
        "current_executable_scientific_target": "none",
        "fresh_response_selector_required": "yes",
        "scientific_target_selected": "no",
        "scientific_execution_authorized": "no",
        "resolved_unit_seam_rows": 0,
        "total_unit_seam_rows": 12,
        "qft_gr_seam": "open",
        "master_action_promoted": "no",
    }
    if live_target == PRIOR_TARGET:
        if prior.get("status") != "active":
            raise V2NonEnrollmentDecisionError(
                "accepted V2 preparation target is not active"
            )
        prior["status"] = "paused"
        prior["live_lane"] = "no"
        prior["v2_preparation_target_disposition"] = "CLOSED_WITHOUT_ACCEPTANCE"
        prior["v2_enrollment_decision"] = "V2_REPRODUCIBLE_BUT_NOT_ENROLLED"
        prior["closure_evidence"] = DECISION_RELATIVE_PATH
        prior["scientific_execution_authorized"] = "no"
        registry["workstreams"].append(waiting_row_contract)
        waiting_row = waiting_row_contract
    else:
        waiting_row = _workstream(registry, WAITING_TARGET)
        if waiting_row != waiting_row_contract:
            raise V2NonEnrollmentDecisionError(
                "existing V2 non-enrollment boundary differs from its frozen contract"
            )
        if prior.get("status") != "paused":
            raise V2NonEnrollmentDecisionError(
                "closed V2 preparation target is not paused"
            )

    state["previous_live_next_target"] = PRIOR_TARGET
    state["live_next_target"] = WAITING_TARGET
    state["live_next_target_kind"] = WAITING_KIND
    state["live_next_target_evidence"] = DECISION_RELATIVE_PATH
    state["live_next_target_report"] = DECISION_RELATIVE_PATH
    state["live_next_target_outcome"] = WAITING_OUTCOME
    state["live_next_target_strict_outcome"] = WAITING_STRICT_OUTCOME
    state["active_lane"] = WAITING_TARGET
    state["active_lanes"] = [WAITING_TARGET]
    state["active_workstream"] = WAITING_TARGET
    state["active_workstream_count"] = 1
    state["active_workstreams"] = [waiting_row]
    state["workstream_id"] = WAITING_TARGET
    state["current_target"] = WAITING_TARGET
    state["current_target_kind"] = WAITING_KIND
    state["current_target_evidence"] = DECISION_RELATIVE_PATH
    state["current_target_report"] = DECISION_RELATIVE_PATH
    state["current_target_outcome"] = WAITING_OUTCOME
    state["current_target_strict_outcome"] = WAITING_STRICT_OUTCOME
    paused = list(state.get("paused_lanes", []))
    if PRIOR_TARGET not in paused:
        paused.append(PRIOR_TARGET)
    state["paused_lanes"] = paused
    state["v2_enrollment_state"] = "V2_REPRODUCIBLE_BUT_NOT_ENROLLED"
    state["v2_preparation_target"] = "CLOSED_WITHOUT_ACCEPTANCE"
    state["current_executable_scientific_target"] = "NONE"
    state["next_scientific_action"] = "REQUIRES_FRESH_RESPONSE_SELECTOR"
    state["scientific_execution_authorized"] = False

    # repair_registry verifies these two pre-repair aliases before regenerating
    # every current projection and read-only root mirror.
    registry["ACTIVE_LANE_v0"] = WAITING_TARGET
    registry["CURRENT_LIVE_NEXT_TARGET_v0"] = WAITING_TARGET
    registry["current_target_coverage"] = [
        DECISION_RELATIVE_PATH,
        "formal/docs/release/CLEAN_INTEGRATION_CANDIDATE_RESULT_REVIEW_20260725_v0.json",
    ]
    registry["current_target_coverage_count"] = 2
    registry["current_target_coverage_size"] = 2
    next_target_coverage = list(registry.get("next_strict_target_coverage", []))
    if WAITING_TARGET not in next_target_coverage:
        next_target_coverage.append(WAITING_TARGET)
    registry["next_strict_target_coverage"] = next_target_coverage

    transitioned = repair_registry(registry)
    validate_registry(transitioned)
    return transitioned


def expected_registry_bytes(path: Path = DEFAULT_REGISTRY_PATH) -> bytes:
    registry = load_registry(path)
    return canonical_json_bytes(transition_registry(registry))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    if args.write:
        expected = expected_registry_bytes(args.registry)
        atomic_write_registry(args.registry, expected)
        return 0

    current = args.registry.read_bytes()
    expected = expected_registry_bytes(args.registry)
    if current != expected:
        raise V2NonEnrollmentDecisionError(
            "registry is still at the pre-decision state; execute --write once"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
