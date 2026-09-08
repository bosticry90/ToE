from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    REGISTRY_PATH,
    _registry_json_bytes,
    open_attempt,
    strict_json_loads,
    validate_registry_extension,
    write_event,
)
from formal.python.tools.loop_control_registry_integrity import (
    atomic_write_registry,
    repair_registry,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_STAGE_5_OPEN_AUTHORITY_20260731_v0.json"
)
AUTHORITY_REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_STAGE_5_OPEN_AUTHORITY_REVIEW_20260731_v0.json"
)
VALIDATION_PATH = (
    RELEASE_ROOT
    / "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_OPEN_VALIDATION_v0.json"
)
PROGRAM_ID = "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"
SEMANTIC_STAGE_ID = "NATIVE_FRONTIER_DECISION"
TARGET = "select_toe_native_frontier_after_repository_wide_evidence_census_v0"
KIND = "toe_post_census_native_frontier_decision_stage_5_open_v0"
EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToePostCensusNativeFrontierDecisionAttemptOpen.lean"
)
REPORT = (
    "formal/docs/release/bounded_program_events/"
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_"
    "ATTEMPT_05_OPEN_v0.json"
)
OUTCOME = "POST_CENSUS_NATIVE_FRONTIER_DECISION_STAGE_5_OPEN"
STRICT_OUTCOME = (
    "STAGE_5_OPEN_FRONTIER_DECISION_ONLY_NO_RANKING_RESULT_FRONTIER_"
    "SELECTION_TRUTH_ADJUDICATION_EVIDENCE_PROMOTION_REPRESENTATION_ACTION_"
    "SEAM_EXECUTION_SUCCESSOR_PROGRAM_OR_MANDATORY_EXIT"
)
PREVIOUS_STAGE_TARGET = "reconcile_toe_current_native_hypothesis_evidence_v0"
EXPECTED_SCOPE_HASH = (
    "639b469cbaf5000a2382d9eb01f248facf65e21d2776c8600c5922a7b5d2f507"
)
FULL_COMMIT_ID_PATTERN = re.compile(r"[0-9a-f]{40}")
OPEN_EXACT_PATH_SET = [
    "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
    (
        "formal/docs/release/"
        "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_OPEN_VALIDATION_v0.json"
    ),
    REPORT,
    (
        "formal/python/tools/"
        "toe_post_census_native_frontier_decision_stage_authorization.py"
    ),
    "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
    (
        "formal/toe_formal/ToeFormal/Derivation/"
        "ToePostCensusNativeFrontierDecisionAttemptOpen.lean"
    ),
    "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
    "formal/toe_formal/ToeFormalAll.lean",
]


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _current_head() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def _write_json(path: Path, value: dict) -> None:
    if path.exists():
        raise ValueError(f"immutable OPEN artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=True, sort_keys=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def _check_authority() -> None:
    authority = _read(AUTHORITY_PATH)
    review = _read(AUTHORITY_REVIEW_PATH)
    if authority["status"] != (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_5_OPEN_ONLY"
    ):
        raise ValueError("Stage 5 OPEN authority is not valid")
    if authority["program_id"] != PROGRAM_ID:
        raise ValueError("Stage 5 OPEN authority program mismatch")
    if authority["authorized_stage"] != {
        "canonical_scope_hash": EXPECTED_SCOPE_HASH,
        "canonical_target": TARGET,
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "stage_number": 5,
    }:
        raise ValueError("Stage 5 OPEN authority does not match the manifest")
    binding = authority["stage_4_input_binding"]
    if binding["claim_count"] != 2673:
        raise ValueError("Stage 4 claim count is not bound")
    if binding["hypothesis_family_count"] != 23:
        raise ValueError("Stage 4 hypothesis-family count is not bound")
    if binding["supported_but_incomplete_claim_count"] != 77:
        raise ValueError("Stage 4 supported-candidate count is not bound")
    if binding["graph_node_count"] != 3239 or binding["graph_edge_count"] != 6822:
        raise ValueError("Stage 4 hypothesis graph is not bound")
    if binding["canonical_promotion_candidate_count"] != 0:
        raise ValueError("Stage 4 promotion boundary is not bound")
    if binding["repository_claim_exhaustion_established"]:
        raise ValueError("repository claim exhaustion may not be asserted")
    limits = authority["workload_limits"]
    if limits["maximum_candidate_families"] != 23:
        raise ValueError("Stage 5 candidate-family cap is not bound")
    if limits["maximum_ranked_candidates"] != 23:
        raise ValueError("Stage 5 ranking cap is not bound")
    if limits["maximum_selected_frontiers"] != 1:
        raise ValueError("Stage 5 one-frontier cap is not bound")
    decision = authority["decision_contract"]
    if decision["maximum_selected_frontiers"] != 1:
        raise ValueError("Stage 5 one-frontier decision is not bound")
    if decision["no_selection_is_valid"] is not True:
        raise ValueError("Stage 5 explicit no-selection result is not permitted")
    if decision["canonical_evidence_promotion"]:
        raise ValueError("Stage 5 may not promote evidence")
    if decision["automatic_next_program_open"]:
        raise ValueError("Stage 5 may not open a successor program")
    if review["accepted"] is not True or not all(review["checks"].values()):
        raise ValueError("Stage 5 OPEN authority review is not accepted")
    if review["decision"] != "AUTHORIZE_STAGE_5_OPEN":
        raise ValueError("Stage 5 OPEN authority review decision mismatch")


def _project_current_target(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 5 target is not current")
    projection.update(
        {
            "active_lane": TARGET,
            "current_target": TARGET,
            "current_target_kind": KIND,
            "current_target_evidence": EVIDENCE,
            "current_target_report": REPORT,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "previous_target": PREVIOUS_STAGE_TARGET,
            "workstream_id": TARGET,
        }
    )
    registry.update(
        {
            "active_lane": TARGET,
            "active_lane_count": 1,
            "ACTIVE_LANE_v0": TARGET,
            "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
            "PREVIOUS_LIVE_NEXT_TARGET_v0": PREVIOUS_STAGE_TARGET,
            "CURRENT_LIVE_TARGET_EVIDENCE_v0": EVIDENCE,
            "CURRENT_LIVE_TARGET_REPORT_v0": REPORT,
            "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT_OUTCOME,
            "CURRENT_LIVE_TARGET_KIND_v0": KIND,
            "current_target": TARGET,
            "current_target_kind": KIND,
            "current_target_evidence": EVIDENCE,
            "current_target_report": REPORT,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "live_next_target": TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": EVIDENCE,
            "live_next_target_report": REPORT,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
            "previous_live_next_target": PREVIOUS_STAGE_TARGET,
            "current_live_next_target": TARGET,
            "current_live_target": TARGET,
            "current_live_target_kind": KIND,
            "current_live_target_evidence": EVIDENCE,
            "current_live_target_report": REPORT,
            "current_live_target_outcome": OUTCOME,
            "current_live_target_strict_outcome": STRICT_OUTCOME,
        }
    )
    active = [
        item for item in registry["workstreams"] if item.get("status") == "active"
    ]
    if len(active) != 1 or active[0]["workstream_id"] != TARGET:
        raise ValueError("expected the selected Stage 5 workstream to be active")
    workstream = active[0]
    workstream.update(
        {
            "queue_scope": (
                "Stage 5 post-census native-frontier decision is OPEN under "
                "immutable bounded-program authority; no ranking or selection "
                "result exists"
            ),
            "selected_next_target_kind": KIND,
            "authorization_evidence": EVIDENCE,
            "report": REPORT,
            "report_path": REPORT,
            "report_sha256": report_sha256,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT_OUTCOME,
            "consumed_target": PREVIOUS_STAGE_TARGET,
            "consumed_target_kind": "closed_bounded_stage_4_scientific_authority",
            "claim_ceiling_level": 2,
            "claim_label": "B-BOUNDED",
            "claim_status": (
                "Stage 5 OPEN only for bounded ranking and selection of one "
                "native frontier or explicit no selection; no result, truth "
                "adjudication, evidence promotion, field, action, seam, "
                "successor program, or mandatory exit"
            ),
        }
    )
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstream_count"] = 1
    registry["active_workstreams"] = [dict(workstream)]
    state = registry["current_target_state"]
    state.update(
        {
            "active_lane": TARGET,
            "live_next_target": TARGET,
            "previous_live_next_target": PREVIOUS_STAGE_TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": EVIDENCE,
            "live_next_target_report": REPORT,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
    )
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    program["program_terminal_status"] = (
        "STAGE_5_OPEN_AWAITING_POST_CENSUS_NATIVE_FRONTIER_DECISION_RESULT"
    )


def _validation_payload(
    *,
    opened_from_commit: str,
    event: dict,
    event_path: Path,
    registry: dict,
) -> dict:
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    return {
        "artifact_id": (
            "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_OPEN_VALIDATION_v0"
        ),
        "attempt_sequence_number": 5,
        "atomic_open_commit_expected_path_count": len(OPEN_EXACT_PATH_SET),
        "atomic_open_commit_expected_paths": OPEN_EXACT_PATH_SET,
        "authority_decision": "AUTHORIZE_STAGE_5_OPEN",
        "bounded_program_state_after_open": program["state"],
        "captured_at_utc": "2026-07-31T07:00:00Z",
        "event_hash": event["event_hash"],
        "event_path": REPORT,
        "event_sha256": _sha256(event_path),
        "event_sequence_number": 9,
        "opened_from_commit": opened_from_commit,
        "program_id": PROGRAM_ID,
        "registry_snapshot_hash": event["registry_snapshot_hash"],
        "schema_id": (
            "toe.post_census_native_frontier_decision."
            "stage_5_open_validation.v0"
        ),
        "scope_hash": EXPECTED_SCOPE_HASH,
        "scientific_output_at_open": {
            "canonical_evidence_promoted": False,
            "frontier_ranking_performed": False,
            "frontier_ranking_result_produced": False,
            "native_frontier_selected": False,
            "next_program_authorized_or_opened": False,
            "representation_action_or_seam_selected": False,
            "scientific_claim_adjudicated": False,
            "stage_5_result_produced": False,
        },
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "stage_4_input_binding": _read(AUTHORITY_PATH)["stage_4_input_binding"],
        "status": "STAGE_5_ATOMIC_OPEN_READY_FOR_COMMIT",
        "target": TARGET,
        "validation_checks": {
            "authority_and_review_accepted": True,
            "canonical_manifest_binding_matches": True,
            "event_and_registry_projection_match": True,
            "open_checkpoint_contains_no_ranking_or_selection_result": True,
            "program_attempt_count_is_five": (
                program["attempted_stage_ids"]
                == [
                    "REPOSITORY_WIDE_SOURCE_CENSUS",
                    "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
                    "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION",
                    "CURRENT_HYPOTHESIS_RECONCILIATION",
                    SEMANTIC_STAGE_ID,
                ]
            ),
            "program_state_is_open": program["state"] == "OPEN",
            "stage_4_close_is_bound": True,
            "truth_adjudication_and_promotion_remain_prohibited": True,
            "one_frontier_or_no_selection_boundary_preserved": True,
            "successor_program_remains_prohibited": True,
            "workload_limits_are_bound": True,
        },
    }


def open_stage(*, opened_from_commit: str) -> str:
    _check_authority()
    if not FULL_COMMIT_ID_PATTERN.fullmatch(opened_from_commit):
        raise ValueError("opened_from_commit must be a lowercase full commit ID")
    if _current_head() != opened_from_commit:
        raise ValueError("opened_from_commit must equal the current HEAD")
    registry_bytes = REGISTRY_PATH.read_bytes()
    registry = strict_json_loads(registry_bytes.decode("utf-8"))
    migrated, relative_path, event = open_attempt(
        registry,
        registry_bytes=registry_bytes,
        program_id=PROGRAM_ID,
        semantic_stage_id=SEMANTIC_STAGE_ID,
        target=TARGET,
        opened_from_commit=opened_from_commit,
    )
    if event["scope_hash"] != EXPECTED_SCOPE_HASH:
        raise ValueError("OPEN event scope hash mismatch")
    if event["attempt_sequence_number"] != 5:
        raise ValueError("OPEN event attempt number mismatch")
    if event["event_sequence_number"] != 9:
        raise ValueError("OPEN event sequence number mismatch")
    event_path = REPO_ROOT / relative_path
    write_event(event_path, event)
    try:
        report_sha256 = _sha256(event_path)
        _project_current_target(migrated, report_sha256)
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        validation = _validation_payload(
            opened_from_commit=opened_from_commit,
            event=event,
            event_path=event_path,
            registry=migrated,
        )
        if not all(validation["validation_checks"].values()):
            raise ValueError("OPEN validation checks did not all pass")
        _write_json(VALIDATION_PATH, validation)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
    except Exception:
        event_path.unlink(missing_ok=True)
        VALIDATION_PATH.unlink(missing_ok=True)
        raise
    return relative_path


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--opened-from-commit", required=True)
    args = parser.parse_args()
    print(open_stage(opened_from_commit=args.opened_from_commit))
