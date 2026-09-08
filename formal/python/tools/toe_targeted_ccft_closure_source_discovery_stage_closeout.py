from __future__ import annotations

"""Review and atomically close targeted CCFT source-discovery Stage 1."""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    raise SystemExit(
        "Run this tool as a module:\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_Path(__file__).stem} --help"
    )

import argparse
import hashlib
import json
import subprocess
from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.tools.bounded_program_governance import (
    REGISTRY_PATH,
    _registry_json_bytes,
    close_attempt,
    strict_json_loads,
    validate_registry_extension,
    write_event,
)
from formal.python.tools.loop_control_registry_integrity import (
    atomic_write_registry,
    repair_registry,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
STAGE_ID = "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY"
STAGE_TARGET = "discover_toe_targeted_ccft_closure_evidence_sources_v0"
NEXT_TARGET = "extract_toe_targeted_ccft_closure_contracts_v0"
RESULT_PATH = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_RESULT_v0.json"
REVIEW_PATH = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_RESULT_REVIEW_v0.json"
VALIDATION_PATH = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_VALIDATION_v0.json"
MANIFEST_PATH = RELEASE_ROOT / "bounded_program_manifests/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
RESULT_RELATIVE = RESULT_PATH.relative_to(REPO_ROOT).as_posix()
REVIEW_RELATIVE = REVIEW_PATH.relative_to(REPO_ROOT).as_posix()
RESULT_MODULE_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/ToeTargetedCCFTClosureSourceDiscoveryResult.lean"
CURRENT_TARGET_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
RESULT_MODULE = "ToeFormal.Derivation.ToeTargetedCCFTClosureSourceDiscoveryResult"
RESULT_KIND = "toe_targeted_ccft_closure_contract_extraction_stage_2_selected_unopened_v0"
OUTCOME = "TARGETED_CCFT_SOURCE_SET_BOUND"
STRICT_OUTCOME = (
    "STAGE_1_CLOSED_PASSED_96_SOURCE_SET_BOUND_ONE_PASS_CONSUMED_NO_CONTRACT_"
    "RECOVERY_EQUATION_REPAIR_POSTULATE_CCFT_V0_CONSTRUCTION_PROMOTION_OR_STAGE_2_OPEN"
)


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_json(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"immutable closeout artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def _head() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _review_result(result: dict[str, Any], captured_at_utc: str) -> dict[str, Any]:
    manifest = _load(MANIFEST_PATH)
    discovery = result["deterministic_candidate_discovery"]
    caps = result["workload_cap_accounting"]
    selected = result["selected_source_ledger"]
    roots = result["source_root_snapshot_records"]
    branch_counts = Counter(row["allocation_branch"] for row in selected)
    identities = [row["verified_sha256"] for row in selected]
    checks = {
        "program_stage_target_and_scope_match_manifest": (
            result["program_id"] == PROGRAM_ID
            and result["semantic_stage_id"] == STAGE_ID
            and result["scientific_target"] == STAGE_TARGET
            and result["scope_hash"] == manifest["stages"][0]["canonical_scope_hash"]
        ),
        "single_content_pass_consumed_exactly_once": (
            result["single_content_pass"]["passes_consumed"] == 1
            and result["single_content_pass"]["authorized_pass_limit"] == 1
            and result["single_content_pass"]["second_search_authorized"] is False
        ),
        "all_eight_roots_are_stable": (
            len(roots) == 8
            and all(row["stability_status"] == "SOURCE_ROOT_SNAPSHOT_STABLE" for row in roots)
        ),
        "immutable_census_population_is_complete": result["source_inventory_summary"]["census_record_count"] == 13563,
        "candidate_population_is_deterministically_bounded": (
            discovery["raw_candidate_path_count"] == 393
            and discovery["metadata_candidate_count"] == 256
            and discovery["metadata_candidate_overflow_count"] == 137
        ),
        "selected_set_hits_the_frozen_file_cap_without_exceeding_it": (
            len(selected) == 96 and caps["deep_review_files_selected"] == 96
        ),
        "branch_allocation_is_balanced_and_within_cap": branch_counts == {"CP_NLSE": 48, "LCRD_V3": 48},
        "selected_content_identities_are_unique": len(identities) == len(set(identities)) == 96,
        "all_selected_sources_were_previously_unreviewed": all(not row["previously_deep_reviewed"] for row in selected),
        "selected_source_and_text_byte_caps_are_respected": (
            caps["selected_source_bytes"] <= caps["maximum_total_deep_review_bytes"]
            and caps["selected_extracted_text_bytes"] <= caps["maximum_total_extracted_text_bytes"]
        ),
        "lineage_cap_is_respected": caps["maximum_selected_in_any_lineage"] <= caps["maximum_deep_review_files_per_lineage"],
        "selected_parser_and_unsupported_caps_are_respected": (
            caps["selected_parser_failure_count"] <= caps["maximum_parser_failures"]
            and caps["selected_unsupported_format_file_count"] <= caps["maximum_unsupported_format_files"]
        ),
        "inventory_visible_excluded_formats_do_not_enter_deep_review": caps["inventory_visible_excluded_records_do_not_count_against_deep_review_budget"] is True,
        "every_selected_source_passes_the_frozen_gate": all(
            row["branch_term_hits"]
            and (row["contract_term_hits"] or row["structural_signature_hits"])
            for row in selected
        ),
        "selected_text_is_hash_bound_for_stage_2_reuse": all(
            hashlib.sha256(row["passive_text_capture"].encode("utf-8")).hexdigest()
            == row["passive_text_capture_sha256"]
            for row in selected
        ),
        "no_contract_extraction_or_adjudication_occurred": all(
            row["scientific_contract_interpretation_performed"] is False
            for row in selected
        ),
        "no_equation_repair_parameter_inference_postulate_or_model_construction_occurred": all(
            value is False for value in result["nonclaim_boundary"].values()
        ),
        "stage_2_is_selected_but_unauthorized": (
            result["stage_2_handoff"]["selected_target"] == NEXT_TARGET
            and result["stage_2_handoff"]["stage_2_authorized"] is False
        ),
        "terminal_outcome_is_the_frozen_positive_stage_1_result": (
            result["terminal_outcome"] == OUTCOME
            and result["lifecycle_result"] == "PASSED"
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise ValueError(f"independent result review failed: {failed}")
    return {
        "artifact_id": "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_RESULT_REVIEW_v0",
        "schema_id": "toe.targeted_ccft_closure.source_discovery_and_custody.result_review.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "semantic_stage_id": STAGE_ID,
        "reviewed_result": {"path": RESULT_RELATIVE, "sha256": _sha(RESULT_PATH)},
        "checks": checks,
        "failed_checks": [],
        "accepted": True,
        "decision": "ACCEPT_TARGETED_CCFT_SOURCE_SET_BOUND_SELECT_STAGE_2_UNOPENED",
        "scientific_interpretation": {
            "candidate_path_count": discovery["raw_candidate_path_count"],
            "metadata_candidate_count": discovery["metadata_candidate_count"],
            "selected_unique_content_count": len(selected),
            "selected_by_branch": dict(sorted(branch_counts.items())),
            "selected_local_custody_source_count": sum(row["local_custody_limitation"] for row in selected),
            "contract_recovery_established": False,
            "candidate_match_establishes_source_authority": False,
        },
        "stage_2_authorized": False,
        "status": "PASS",
    }


def _project_next_target(registry: dict[str, Any], result_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != STAGE_TARGET:
        raise ValueError("open Stage-1 target is not current")
    evidence = "formal/toe_formal/ToeFormal/Derivation/ToeTargetedCCFTClosureSourceDiscoveryResult.lean"
    report = RESULT_RELATIVE
    projection.update(
        {
            "active_lane": NEXT_TARGET,
            "current_target": NEXT_TARGET,
            "current_target_kind": RESULT_KIND,
            "current_target_evidence": evidence,
            "current_target_report": report,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "previous_target": STAGE_TARGET,
            "workstream_id": NEXT_TARGET,
        }
    )
    registry.update(
        {
            "active_lane": NEXT_TARGET,
            "ACTIVE_LANE_v0": NEXT_TARGET,
            "CURRENT_LIVE_NEXT_TARGET_v0": NEXT_TARGET,
            "PREVIOUS_LIVE_NEXT_TARGET_v0": STAGE_TARGET,
            "CURRENT_LIVE_TARGET_EVIDENCE_v0": evidence,
            "CURRENT_LIVE_TARGET_REPORT_v0": report,
            "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT_OUTCOME,
            "CURRENT_LIVE_TARGET_KIND_v0": RESULT_KIND,
            "current_live_next_target": NEXT_TARGET,
            "current_live_target": NEXT_TARGET,
            "current_live_target_evidence": evidence,
            "current_live_target_kind": RESULT_KIND,
            "current_live_target_outcome": OUTCOME,
            "current_live_target_report": report,
            "current_live_target_strict_outcome": STRICT_OUTCOME,
            "current_target": NEXT_TARGET,
            "current_target_evidence": evidence,
            "current_target_kind": RESULT_KIND,
            "current_target_outcome": OUTCOME,
            "current_target_report": report,
            "current_target_strict_outcome": STRICT_OUTCOME,
            "live_next_target": NEXT_TARGET,
            "live_next_target_evidence": evidence,
            "live_next_target_kind": RESULT_KIND,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_report": report,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
    )
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != STAGE_TARGET:
        raise ValueError("active workstream is not open targeted discovery")
    workstream = active[0]
    workstream.update(
        {
            "workstream_id": NEXT_TARGET,
            "active_lane": NEXT_TARGET,
            "authorized_target": NEXT_TARGET,
            "authorized_next_strict_target": NEXT_TARGET,
            "selected_next_target": NEXT_TARGET,
            "selected_next_target_kind": RESULT_KIND,
            "authorization_evidence": evidence,
            "report": report,
            "report_path": report,
            "report_sha256": result_sha256,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT_OUTCOME,
            "consumed_target": STAGE_TARGET,
            "consumed_target_kind": "completed_bounded_scientific_stage",
            "queue_scope": "Stage 1 closed with a custody-bound 96-source set; contract extraction remains separately unauthorized",
            "claim_status": "Candidate discovery only; no contract recovery equation repair postulate CCFT-v0 construction promotion or Stage 2 OPEN",
        }
    )
    registry["active_lanes"] = [NEXT_TARGET]
    registry["active_workstream"] = NEXT_TARGET
    registry["active_workstreams"] = [dict(workstream)]
    coverage = registry["next_strict_target_coverage"]
    if NEXT_TARGET not in coverage:
        coverage.append(NEXT_TARGET)
        coverage.sort()
    registry["current_target_state"].update(
        {
            "active_lane": NEXT_TARGET,
            "live_next_target": NEXT_TARGET,
            "previous_live_next_target": STAGE_TARGET,
            "live_next_target_kind": RESULT_KIND,
            "live_next_target_evidence": evidence,
            "live_next_target_report": report,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
    )


def _write_lean(result: dict[str, Any]) -> None:
    discovery = result["deterministic_candidate_discovery"]
    caps = result["workload_cap_accounting"]
    result_text = f'''namespace ToeFormal
namespace Derivation
namespace ToeTargetedCCFTClosureSourceDiscoveryResult

def resultId : String := "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_RESULT_v0"
def reviewId : String := "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_RESULT_REVIEW_v0"
def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{STAGE_ID}"
def terminalOutcome : String := "{OUTCOME}"
def selectedNextTarget : String := "{NEXT_TARGET}"

def attemptSequenceNumber : Nat := 1
def authorizedRootCount : Nat := 8
def censusRecordCount : Nat := 13563
def contentPassesConsumed : Nat := 1
def rawCandidatePathCount : Nat := {discovery['raw_candidate_path_count']}
def metadataCandidateCount : Nat := {discovery['metadata_candidate_count']}
def metadataCandidateOverflowCount : Nat := {discovery['metadata_candidate_overflow_count']}
def selectedSourceCount : Nat := {discovery['selected_unique_content_count']}
def cpNlseSelectedCount : Nat := {discovery['selected_by_branch']['CP_NLSE']}
def lcrdV3SelectedCount : Nat := {discovery['selected_by_branch']['LCRD_V3']}
def selectedSourceBytes : Nat := {caps['selected_source_bytes']}
def selectedExtractedTextBytes : Nat := {caps['selected_extracted_text_bytes']}

def allRootsStable : Bool := true
def contractRecoveryPerformed : Bool := false
def equationRepairPerformed : Bool := false
def newCCFTPostulateInserted : Bool := false
def ccftV0Constructed : Bool := false
def evidencePromoted : Bool := false
def repositoryClaimExhaustionEstablished : Bool := false
def stageTwoAuthorized : Bool := false
def reviewAccepted : Bool := true

theorem source_set_is_bounded_and_balanced :
    terminalOutcome = "TARGETED_CCFT_SOURCE_SET_BOUND" ∧
    attemptSequenceNumber = 1 ∧ authorizedRootCount = 8 ∧
    censusRecordCount = 13563 ∧ contentPassesConsumed = 1 ∧
    rawCandidatePathCount = 393 ∧ metadataCandidateCount = 256 ∧
    metadataCandidateOverflowCount = 137 ∧ selectedSourceCount = 96 ∧
    cpNlseSelectedCount = 48 ∧ lcrdV3SelectedCount = 48 ∧
    allRootsStable = true ∧ reviewAccepted = true := by
  decide

theorem discovery_remains_nonextractive_nonconstructive_and_unopened :
    contractRecoveryPerformed = false ∧ equationRepairPerformed = false ∧
    newCCFTPostulateInserted = false ∧ ccftV0Constructed = false ∧
    evidencePromoted = false ∧ repositoryClaimExhaustionEstablished = false ∧
    stageTwoAuthorized = false := by
  decide

end ToeTargetedCCFTClosureSourceDiscoveryResult
end Derivation
end ToeFormal
'''
    RESULT_MODULE_PATH.write_text(result_text, encoding="utf-8", newline="\n")
    current_target = f'''import {RESULT_MODULE}

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTClosureSourceDiscoveryResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := selectedNextTarget
def currentEvidencePacketId : String := resultId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "CLOSED"
def currentTargetPhase : String :=
  "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_STAGE_1_CLOSED_PASSED"
def currentBoundedAttemptNumber : Nat := attemptSequenceNumber
def lastClosedBoundedSemanticStage : String := semanticStageId
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_contract_extraction_without_authorizing_it :
    currentLiveTarget = "{NEXT_TARGET}" ∧
    currentBoundedProgramId = "{PROGRAM_ID}" ∧
    currentBoundedProgramState = "CLOSED" ∧
    currentBoundedAttemptNumber = 1 ∧ selectedSourceCount = 96 ∧
    contentPassesConsumed = 1 ∧ contractRecoveryPerformed = false ∧
    stageTwoAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
'''
    CURRENT_TARGET_PATH.write_text(current_target, encoding="utf-8", newline="\n")
    current_authority = f'''import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def boundedProgramId : String := Derivation.CurrentTarget.currentBoundedProgramId
def boundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def boundedAttemptNumber : Nat := Derivation.CurrentTarget.currentBoundedAttemptNumber

theorem current_authority_tracks_selected_unopened_contract_extraction :
    currentTarget = "{NEXT_TARGET}" ∧
    boundedProgramId = "{PROGRAM_ID}" ∧ boundedProgramState = "CLOSED" ∧
    boundedAttemptNumber = 1 ∧
    Derivation.ToeTargetedCCFTClosureSourceDiscoveryResult.terminalOutcome =
      "{OUTCOME}" ∧
    Derivation.ToeTargetedCCFTClosureSourceDiscoveryResult.stageTwoAuthorized = false := by
  native_decide

theorem bounded_program_governance_installation_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" ∧
    BoundedProgramGovernanceControlInstallationV0.scientificTargetRotated = false := by
  native_decide

theorem bounded_program_governance_review_preserved_its_then_current_target :
    BoundedProgramGovernanceControlInstallationResultReviewV0.scientificTarget =
      "prepare_qft_gr_quadratic_generic_background_linearization_gauge_and_jet_contract_v0" := by
  native_decide

theorem stage_one_authority_and_review_remain_bound :
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0.stageOneOpenAuthorized =
      true ∧
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0.accepted =
      true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
'''
    CURRENT_AUTHORITY_PATH.write_text(current_authority, encoding="utf-8", newline="\n")


def close_stage(*, closed_from_commit: str, captured_at_utc: str) -> str:
    if _head() != closed_from_commit:
        raise ValueError("closed_from_commit must equal current HEAD")
    result = _load(RESULT_PATH)
    review = _review_result(result, captured_at_utc)
    _write_json(REVIEW_PATH, review)
    registry = strict_json_loads(REGISTRY_PATH.read_text(encoding="utf-8"))
    migrated, relative_event_path, event = close_attempt(
        registry,
        program_id=PROGRAM_ID,
        result_artifact_path=RESULT_RELATIVE,
        review_artifact_path=REVIEW_RELATIVE,
        terminal_result="PASSED",
        closed_from_commit=closed_from_commit,
    )
    event_path = REPO_ROOT / relative_event_path
    write_event(event_path, event)
    try:
        _project_next_target(migrated, _sha(RESULT_PATH))
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        _write_lean(result)
        manifest = _load(MANIFEST_PATH)
        validation = {
            "artifact_id": "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_VALIDATION_v0",
            "schema_id": "toe.targeted_ccft_closure.source_discovery_and_custody.validation.v0",
            "captured_at_utc": captured_at_utc,
            "program_id": PROGRAM_ID,
            "semantic_stage_id": STAGE_ID,
            "terminal_outcome": OUTCOME,
            "lifecycle_result": "PASSED",
            "artifact_hashes": {
                "result_sha256": _sha(RESULT_PATH),
                "review_sha256": _sha(REVIEW_PATH),
                "close_event_sha256": _sha(event_path),
                "close_event_hash": event["event_hash"],
            },
            "atomic_close_commit_expected_paths": manifest["stages"][0]["prospective_envelope"]["close_commit_exact_path_set"],
            "scientific_validation": review["checks"],
            "focused_python": {"status": "PENDING_PRECOMMIT"},
            "focused_lean": {"status": "PENDING_PRECOMMIT"},
            "full_lean_aggregate": {"status": "PENDING_PRECOMMIT"},
            "deterministic_generation": {"status": "PENDING_PRECOMMIT"},
            "governance_validation": {
                "event_hash_and_open_close_linkage": "PASS_PRECOMMIT",
                "git_history_chronology": "REQUIRED_POST_COMMIT",
                "precommit_full_history_validator_result": "EXPECTED_SINGLE_FAILURE_CLOSE_ARTIFACT_HAS_ZERO_INTRODUCTION_COMMITS",
            },
            "repository_validation": {
                "exhaustive_python_status": "NOT_CLAIMED_HISTORICAL_DEBT_REMAINS",
                "git_diff_check": "PENDING_PRECOMMIT",
                "reddit_status": "UNTRACKED_AND_UNTOUCHED",
                "tracked_checkout_after_close_commit": "REQUIRED_POST_COMMIT",
            },
            "status": "STAGE_1_ATOMIC_CLOSE_READY_FOR_VALIDATION",
        }
        _write_json(VALIDATION_PATH, validation)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
    except Exception:
        REVIEW_PATH.unlink(missing_ok=True)
        event_path.unlink(missing_ok=True)
        VALIDATION_PATH.unlink(missing_ok=True)
        RESULT_MODULE_PATH.unlink(missing_ok=True)
        raise
    return relative_event_path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--closed-from-commit", required=True)
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args(argv)
    print(
        close_stage(
            closed_from_commit=args.closed_from_commit,
            captured_at_utc=args.captured_at_utc,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
