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
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
AUTHORITY_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_SOURCE_CENSUS_STAGE_1_OPEN_AUTHORITY_20260730_v0.json"
)
AUTHORITY_REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_SOURCE_CENSUS_STAGE_1_OPEN_AUTHORITY_REVIEW_20260730_v0.json"
)
DEPENDENCY_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_CENSUS_STAGE_1_DEPENDENCY_IMPACT_CHECK_20260730_v0.json"
)
VALIDATION_PATH = (
    RELEASE_ROOT
    / "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_SOURCE_CENSUS_OPEN_VALIDATION_v0.json"
)
PROGRAM_ID = "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"
SEMANTIC_STAGE_ID = "REPOSITORY_WIDE_SOURCE_CENSUS"
TARGET = "inventory_toe_repository_wide_native_hypothesis_sources_v0"
KIND = "toe_repository_wide_native_hypothesis_source_census_stage_1_open_v0"
EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.lean"
)
REPORT = (
    "formal/docs/release/bounded_program_events/"
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_"
    "ATTEMPT_01_OPEN_v0.json"
)
OUTCOME = "REPOSITORY_WIDE_SOURCE_CENSUS_STAGE_1_OPEN"
STRICT_OUTCOME = (
    "STAGE_1_OPEN_NO_SOURCE_CENSUS_OUTPUT_CLAIM_EXTRACTION_LINEAGE_"
    "PROMOTION_FRONTIER_SELECTION_OR_STAGE_2"
)
EXPECTED_PREVIOUS_TARGET = (
    "prepare_toe_repository_wide_native_hypothesis_evidence_census_"
    "bounded_program_v0"
)
EXPECTED_SCOPE_HASH = (
    "be877b7daf4bb24fa5fa9c49c75891394d8bb16ddf6e2658d7e7360fba94da64"
)
FULL_COMMIT_ID_PATTERN = re.compile(r"[0-9a-f]{40}")
OPEN_EXACT_PATH_SET = [
    "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
    (
        "formal/docs/release/"
        "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_SOURCE_CENSUS_"
        "OPEN_VALIDATION_v0.json"
    ),
    REPORT,
    (
        "formal/python/tools/"
        "toe_repository_wide_native_hypothesis_source_census_"
        "stage_authorization.py"
    ),
    "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
    (
        "formal/toe_formal/ToeFormal/Derivation/"
        "ToeRepositoryWideNativeHypothesisSourceCensusAttemptOpen.lean"
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
    dependency = _read(DEPENDENCY_PATH)
    if authority["status"] != (
        "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_1_OPEN_ONLY"
    ):
        raise ValueError("Stage 1 OPEN authority is not valid")
    if authority["program_id"] != PROGRAM_ID:
        raise ValueError("Stage 1 OPEN authority program mismatch")
    if authority["authorized_stage"] != {
        "canonical_scope_hash": EXPECTED_SCOPE_HASH,
        "canonical_target": TARGET,
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "stage_number": 1,
    }:
        raise ValueError("Stage 1 OPEN authority does not match the manifest")
    if len(authority["authorized_batches"]) != 8:
        raise ValueError("Stage 1 OPEN authority must bind exactly eight batches")
    if authority["file_and_byte_limits"]["stage_1_claim_extraction_limit"] != 0:
        raise ValueError("claim extraction is not permitted in Stage 1")
    if authority["file_and_byte_limits"]["stage_1_deep_review_limit"] != 0:
        raise ValueError("deep review is not permitted in Stage 1")
    if authority["custody_and_portability"]["reddit_excluded"] is not True:
        raise ValueError("reddit exclusion is not bound")
    if review["accepted"] is not True or not all(review["checks"].values()):
        raise ValueError("Stage 1 OPEN authority review is not accepted")
    if review["decision"] != (
        "AUTHORIZE_REPOSITORY_WIDE_SOURCE_CENSUS_STAGE_1_OPEN"
    ):
        raise ValueError("Stage 1 OPEN authority review decision mismatch")
    if dependency["stage_1_open_permitted_by_dependency_check"] is not True:
        raise ValueError("Stage 1 dependency-impact check blocks OPEN")
    if dependency["exhaustive_python_debt"]["exhaustive_passage_established"]:
        raise ValueError("dependency record incorrectly claims exhaustive passage")


def _project_current_target(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != EXPECTED_PREVIOUS_TARGET:
        raise ValueError("program-preparation target is not current")
    projection.update(
        {
            "active_lane": TARGET,
            "current_target": TARGET,
            "current_target_kind": KIND,
            "current_target_evidence": EVIDENCE,
            "current_target_report": REPORT,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "previous_target": EXPECTED_PREVIOUS_TARGET,
            "workstream_id": TARGET,
        }
    )
    registry.update(
        {
            "active_lane": TARGET,
            "ACTIVE_LANE_v0": TARGET,
            "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
            "PREVIOUS_LIVE_NEXT_TARGET_v0": EXPECTED_PREVIOUS_TARGET,
            "CURRENT_LIVE_TARGET_EVIDENCE_v0": EVIDENCE,
            "CURRENT_LIVE_TARGET_REPORT_v0": REPORT,
            "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT_OUTCOME,
            "CURRENT_LIVE_TARGET_KIND_v0": KIND,
        }
    )
    previous_active = [
        item for item in registry["workstreams"] if item.get("status") == "active"
    ]
    if len(previous_active) != 1:
        raise ValueError("expected exactly one active predecessor workstream")
    workstream = previous_active[0]
    if workstream["workstream_id"] != EXPECTED_PREVIOUS_TARGET:
        raise ValueError("active workstream is not the program-preparation target")
    workstream.update(
        {
            "workstream_id": TARGET,
            "active_lane": TARGET,
            "authorized_target": TARGET,
            "authorized_next_strict_target": TARGET,
            "selected_next_target": TARGET,
            "selected_next_target_kind": KIND,
            "authorization_evidence": EVIDENCE,
            "report": REPORT,
            "report_path": REPORT,
            "report_sha256": report_sha256,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT_OUTCOME,
            "consumed_target": EXPECTED_PREVIOUS_TARGET,
            "consumed_target_kind": "previous_scientific_authority",
            "queue_scope": (
                "Stage 1 repository-wide source and custody census is OPEN; "
                "no scientific census output exists in the OPEN checkpoint"
            ),
            "claim_status": (
                "Stage 1 OPEN only; no source census output, claim extraction, "
                "lineage conclusion, evidence promotion, frontier selection, "
                "field, action, seam, observable, empirical claim, or Stage 2"
            ),
        }
    )
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstreams"] = [dict(workstream)]
    coverage = registry["next_strict_target_coverage"]
    if TARGET not in coverage:
        coverage.append(TARGET)
        coverage.sort()
    state = registry["current_target_state"]
    state.update(
        {
            "active_lane": TARGET,
            "live_next_target": TARGET,
            "previous_live_next_target": EXPECTED_PREVIOUS_TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": EVIDENCE,
            "live_next_target_report": REPORT,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
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
            "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_SOURCE_CENSUS_"
            "OPEN_VALIDATION_v0"
        ),
        "attempt_sequence_number": 1,
        "atomic_open_commit_expected_path_count": len(OPEN_EXACT_PATH_SET),
        "atomic_open_commit_expected_paths": OPEN_EXACT_PATH_SET,
        "authority_decision": (
            "AUTHORIZE_REPOSITORY_WIDE_SOURCE_CENSUS_STAGE_1_OPEN"
        ),
        "bounded_program_state_after_open": program["state"],
        "captured_at_utc": "2026-07-30T00:00:00Z",
        "event_hash": event["event_hash"],
        "event_path": REPORT,
        "event_sha256": _sha256(event_path),
        "event_sequence_number": 1,
        "exhaustive_python_passage_claimed": False,
        "opened_from_commit": opened_from_commit,
        "program_id": PROGRAM_ID,
        "registry_snapshot_hash": event["registry_snapshot_hash"],
        "schema_id": (
            "toe.repository_wide_native_hypothesis_source_census."
            "stage_1_open_validation.v0"
        ),
        "scope_hash": EXPECTED_SCOPE_HASH,
        "scientific_output_at_open": {
            "archive_scientifically_traversed": False,
            "authoritative_census_index_generated": False,
            "claim_extraction_performed": False,
            "evidence_promoted": False,
            "lineage_conclusion_produced": False,
            "native_frontier_selected": False,
            "stage_2_output_produced": False,
        },
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "status": "STAGE_1_ATOMIC_OPEN_READY_FOR_COMMIT",
        "target": TARGET,
        "validation_checks": {
            "authority_and_review_accepted": True,
            "canonical_manifest_binding_matches": True,
            "dependency_impact_check_permits_open": True,
            "eight_batches_bound": True,
            "event_and_registry_projection_match": True,
            "exhaustive_python_debt_disclosed": True,
            "open_checkpoint_contains_no_census_output": True,
            "program_attempt_count_is_one": (
                program["attempted_stage_ids"] == [SEMANTIC_STAGE_ID]
            ),
            "program_state_is_open": program["state"] == "OPEN",
            "reddit_excluded": True,
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
    event_path = REPO_ROOT / relative_path
    write_event(event_path, event)
    try:
        report_sha256 = _sha256(event_path)
        _project_current_target(migrated, report_sha256)
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
