from __future__ import annotations

"""Independently review and atomically close targeted CCFT Stage 2."""

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
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry, repair_registry
from formal.python.tools.toe_targeted_ccft_closure_contract_extraction_stage_execution import (
    CHECKLISTS,
    EVIDENCE_CLASSES,
    MANIFEST,
    NEXT_TARGET,
    OPEN_EVENT,
    OUTCOME,
    PROGRAM_ID,
    RELEASE_ROOT,
    REPO_ROOT,
    RESULT_PATH,
    STAGE1_RESULT,
    STAGE_ID,
    TARGET,
)


REVIEW_PATH = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_RESULT_REVIEW_v0.json"
VALIDATION_PATH = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_VALIDATION_v0.json"
RESULT_RELATIVE = RESULT_PATH.relative_to(REPO_ROOT).as_posix()
REVIEW_RELATIVE = REVIEW_PATH.relative_to(REPO_ROOT).as_posix()
RESULT_MODULE_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/ToeTargetedCCFTClosureContractExtractionResult.lean"
CURRENT_TARGET_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_PATH = REPO_ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
RESULT_MODULE = "ToeFormal.Derivation.ToeTargetedCCFTClosureContractExtractionResult"
RESULT_KIND = "toe_targeted_ccft_contract_completeness_and_conflict_adjudication_stage_3_selected_unopened_v0"
STRICT_OUTCOME = (
    "STAGE_2_CLOSED_PASSED_FIXED_96_SOURCE_CONTRACT_EVIDENCE_EXTRACTED_"
    "NO_CONTRACT_ADJUDICATION_EQUATION_REPAIR_POSTULATE_CCFT_V0_CONSTRUCTION_"
    "PROMOTION_OR_STAGE_3_OPEN"
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
        ["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, check=True,
        capture_output=True, text=True,
    ).stdout.strip()


def _manifest_stage() -> dict[str, Any]:
    manifest = _load(MANIFEST)
    return next(stage for stage in manifest["stages"] if stage["stage_number"] == 2)


def _review_result(result: dict[str, Any], captured_at_utc: str) -> dict[str, Any]:
    stage1 = _load(STAGE1_RESULT)
    sources = {row["custody_relative_path"]: row for row in stage1["selected_source_ledger"]}
    records = result["source_bound_contract_record_ledger"]
    source_ledger = result["source_review_ledger"]
    checklist = result["missing_contract_checklist_ledger"]
    caps = result["workload_cap_accounting"]
    summary = result["extraction_summary"]
    record_ids = [row["contract_record_id"] for row in records]
    class_counts = Counter(row["evidence_strength_classification"] for row in records)
    branch_counts = Counter(row["ccft_branch"] for row in records)

    excerpt_checks = []
    for record in records:
        binding = record["source_record_id_path_hash_lineage_and_custody"]
        source = sources[binding["custody_relative_path"]]
        excerpt = record["bounded_supporting_excerpt_and_location"]
        lines = source["passive_text_capture"].splitlines()
        reconstructed = "\n".join(lines[excerpt["line_start"] - 1:excerpt["line_end"]])
        excerpt_checks.append(
            binding["verified_sha256"] == source["verified_sha256"]
            and binding["passive_text_capture_sha256"] == source["passive_text_capture_sha256"]
            and reconstructed == excerpt["text"]
            and hashlib.sha256(reconstructed.encode("utf-8")).hexdigest() == excerpt["excerpt_sha256"]
            and source["allocation_branch"] == record["ccft_branch"]
        )

    expected_pairs = {(branch, item) for branch, items in CHECKLISTS.items() for item in items}
    actual_pairs = {(row["ccft_branch"], row["missing_contract_id"]) for row in checklist}
    checks = {
        "program_stage_target_and_scope_match_manifest": (
            result["program_id"] == PROGRAM_ID
            and result["semantic_stage_id"] == STAGE_ID
            and result["scientific_target"] == TARGET
            and result["scope_hash"] == _manifest_stage()["canonical_scope_hash"]
        ),
        "attempt_two_open_event_is_bound": (
            result["attempt_sequence_number"] == 2
            and result["open_event_binding"]["sha256"] == _sha(OPEN_EVENT)
        ),
        "immutable_stage_one_result_is_bound": result["frozen_stage_1_input"]["sha256"] == _sha(STAGE1_RESULT),
        "fixed_96_source_set_is_complete_and_balanced": (
            len(source_ledger) == 96
            and Counter(row["allocation_branch"] for row in source_ledger) == {"CP_NLSE": 48, "LCRD_V3": 48}
        ),
        "overflow_and_new_search_are_excluded": (
            result["frozen_stage_1_input"]["overflow_sources_used"] == 0
            and result["frozen_stage_1_input"]["new_source_search_or_root_traversal_performed"] is False
            and all(row["new_root_traversal_performed"] is False for row in source_ledger)
        ),
        "all_contract_records_have_unique_ids": len(record_ids) == len(set(record_ids)),
        "all_contract_records_use_frozen_classes": all(
            row["evidence_strength_classification"] in EVIDENCE_CLASSES - {"NO_RELEVANT_EVIDENCE"}
            for row in records
        ),
        "every_excerpt_reverifies_against_its_frozen_capture": bool(records) and all(excerpt_checks),
        "all_18_checklist_items_are_accounted_for_once": len(checklist) == 18 and actual_pairs == expected_pairs,
        "source_ledger_accounts_for_every_record": sorted(
            item for row in source_ledger for item in row["contract_record_ids"]
        ) == sorted(record_ids),
        "summary_counts_close_exactly": (
            summary["record_count"] == len(records)
            and summary["records_by_branch"] == dict(sorted(branch_counts.items()))
            and summary["records_by_evidence_class"] == dict(sorted(class_counts.items()))
            and summary["sources_with_material_evidence"] + summary["sources_with_no_relevant_evidence"] == 96
            and summary["checklists_with_exact_candidates"]
            + summary["checklists_with_conflicts"]
            + summary["checklists_with_only_nonexact_evidence"]
            + summary["checklists_with_no_relevant_evidence"] == 18
        ),
        "record_and_conflict_caps_are_respected": (
            caps["contract_records_extracted"] <= caps["contract_record_cap"] == 192
            and caps["largest_records_for_one_missing_contract"] <= caps["maximum_records_per_missing_contract"] == 12
            and caps["conflicting_records_extracted"] <= caps["conflicting_record_cap"] == 32
        ),
        "parser_cap_is_respected": caps["parser_failures"] <= caps["parser_failure_cap"] == 8,
        "no_contract_adjudication_repair_postulate_construction_or_promotion_occurred": all(
            value is False for value in result["adjudication_boundary"].values()
        ),
        "stage_three_is_selected_but_unauthorized": (
            result["stage_3_handoff"]["selected_target"] == NEXT_TARGET
            and result["stage_3_handoff"]["stage_3_authorized"] is False
        ),
        "terminal_outcome_is_frozen_stage_two_pass": (
            result["terminal_outcome"] == OUTCOME and result["lifecycle_result"] == "PASSED"
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise ValueError(f"independent Stage-2 result review failed: {failed}")
    return {
        "artifact_id": "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_RESULT_REVIEW_v0",
        "schema_id": "toe.targeted_ccft_closure.contract_extraction.result_review.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "semantic_stage_id": STAGE_ID,
        "reviewed_result": {"path": RESULT_RELATIVE, "sha256": _sha(RESULT_PATH)},
        "checks": checks,
        "failed_checks": [],
        "accepted": True,
        "decision": "ACCEPT_CONTRACT_EXTRACTION_SELECT_STAGE_3_UNOPENED",
        "scientific_interpretation": {
            "contract_records_extracted": len(records),
            "records_by_branch": dict(sorted(branch_counts.items())),
            "records_by_evidence_class": dict(sorted(class_counts.items())),
            "contract_recovery_or_rejection_established": False,
            "exact_class_means_candidate_for_stage_3_not_final_adjudication": True,
        },
        "stage_3_authorized": False,
        "status": "PASS",
    }


def _project_next_target(registry: dict[str, Any], result_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("open Stage-2 target is not current")
    evidence = "formal/toe_formal/ToeFormal/Derivation/ToeTargetedCCFTClosureContractExtractionResult.lean"
    report = RESULT_RELATIVE
    projection.update({
        "active_lane": NEXT_TARGET,
        "current_target": NEXT_TARGET,
        "current_target_kind": RESULT_KIND,
        "current_target_evidence": evidence,
        "current_target_report": report,
        "current_target_outcome": OUTCOME,
        "current_target_strict_outcome": STRICT_OUTCOME,
        "previous_target": TARGET,
        "workstream_id": NEXT_TARGET,
    })
    registry.update({
        "active_lane": NEXT_TARGET,
        "ACTIVE_LANE_v0": NEXT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0": NEXT_TARGET,
        "PREVIOUS_LIVE_NEXT_TARGET_v0": TARGET,
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
    })
    active = [item for item in registry["workstreams"] if item.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != TARGET:
        raise ValueError("active workstream is not open contract extraction")
    workstream = active[0]
    workstream.update({
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
        "consumed_target": TARGET,
        "consumed_target_kind": "completed_bounded_scientific_stage",
        "queue_scope": "Stage 2 closed with source-bound extraction only; completeness and conflict adjudication remains separately unauthorized",
        "claim_status": "Evidence extracted; no contract adjudication equation repair postulate CCFT-v0 construction promotion or Stage 3 OPEN",
    })
    registry["active_lanes"] = [NEXT_TARGET]
    registry["active_workstream"] = NEXT_TARGET
    registry["active_workstreams"] = [dict(workstream)]
    coverage = registry["next_strict_target_coverage"]
    if NEXT_TARGET not in coverage:
        coverage.append(NEXT_TARGET)
        coverage.sort()
    registry["current_target_state"].update({
        "active_lane": NEXT_TARGET,
        "live_next_target": NEXT_TARGET,
        "previous_live_next_target": TARGET,
        "live_next_target_kind": RESULT_KIND,
        "live_next_target_evidence": evidence,
        "live_next_target_report": report,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_strict_outcome": STRICT_OUTCOME,
    })


def _write_lean(result: dict[str, Any]) -> None:
    summary = result["extraction_summary"]
    classes = summary["records_by_evidence_class"]
    def class_count(name: str) -> int:
        return classes.get(name, 0)
    result_text = f'''namespace ToeFormal
namespace Derivation
namespace ToeTargetedCCFTClosureContractExtractionResult

def resultId : String := "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_RESULT_v0"
def reviewId : String := "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_RESULT_REVIEW_v0"
def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{STAGE_ID}"
def terminalOutcome : String := "{OUTCOME}"
def selectedNextTarget : String := "{NEXT_TARGET}"

def attemptSequenceNumber : Nat := 2
def frozenSourceCount : Nat := 96
def overflowSourcesUsed : Nat := 0
def contentPassesConsumed : Nat := 1
def contractRecordCount : Nat := {summary['record_count']}
def cpNlseRecordCount : Nat := {summary['records_by_branch'].get('CP_NLSE', 0)}
def lcrdV3RecordCount : Nat := {summary['records_by_branch'].get('LCRD_V3', 0)}
def exactCandidateRecordCount : Nat := {class_count('EXACT_SOURCE_BOUND_CONTRACT_RECOVERED')}
def partialRecordCount : Nat := {class_count('PARTIAL_CONTRACT_RECOVERED')}
def conflictingRecordCount : Nat := {class_count('CONFLICTING_SOURCE_CONTRACTS')}
def derivedSummaryRecordCount : Nat := {class_count('DERIVED_SUMMARY_WITH_PRIMARY_SOURCE_MISSING')}
def numericalDefaultRecordCount : Nat := {class_count('NUMERICAL_DEFAULT_ONLY')}
def heuristicRecordCount : Nat := {class_count('HEURISTIC_NOT_A_CONTRACT')}
def checklistCount : Nat := 18

def contractAdjudicationPerformed : Bool := false
def equationRepairPerformed : Bool := false
def newCCFTPostulateInserted : Bool := false
def ccftV0Constructed : Bool := false
def evidencePromoted : Bool := false
def repositoryClaimExhaustionEstablished : Bool := false
def stageThreeAuthorized : Bool := false
def reviewAccepted : Bool := true

theorem extraction_counts_close_and_remain_bounded :
    terminalOutcome = "{OUTCOME}" ∧ attemptSequenceNumber = 2 ∧
    frozenSourceCount = 96 ∧ overflowSourcesUsed = 0 ∧ contentPassesConsumed = 1 ∧
    contractRecordCount = cpNlseRecordCount + lcrdV3RecordCount ∧
    contractRecordCount = exactCandidateRecordCount + partialRecordCount +
      conflictingRecordCount + derivedSummaryRecordCount + numericalDefaultRecordCount +
      heuristicRecordCount ∧ checklistCount = 18 ∧ reviewAccepted = true := by
  decide

theorem extraction_is_nonadjudicative_nonconstructive_and_stage_three_unopened :
    contractAdjudicationPerformed = false ∧ equationRepairPerformed = false ∧
    newCCFTPostulateInserted = false ∧ ccftV0Constructed = false ∧
    evidencePromoted = false ∧ repositoryClaimExhaustionEstablished = false ∧
    stageThreeAuthorized = false := by
  decide

end ToeTargetedCCFTClosureContractExtractionResult
end Derivation
end ToeFormal
'''
    RESULT_MODULE_PATH.write_text(result_text, encoding="utf-8", newline="\n")
    CURRENT_TARGET_PATH.write_text(f'''import {RESULT_MODULE}

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeTargetedCCFTClosureContractExtractionResult

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := selectedNextTarget
def currentEvidencePacketId : String := resultId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := "CLOSED"
def currentTargetPhase : String := "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_STAGE_2_CLOSED_PASSED"
def currentBoundedAttemptNumber : Nat := attemptSequenceNumber
def lastClosedBoundedSemanticStage : String := semanticStageId
def lastBoundedTerminalResult : String := "PASSED"

theorem current_target_selects_adjudication_without_authorizing_it :
    currentLiveTarget = "{NEXT_TARGET}" ∧ currentBoundedProgramId = "{PROGRAM_ID}" ∧
    currentBoundedProgramState = "CLOSED" ∧ currentBoundedAttemptNumber = 2 ∧
    frozenSourceCount = 96 ∧ contractRecordCount > 0 ∧
    contractAdjudicationPerformed = false ∧ stageThreeAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_AUTHORITY_PATH.write_text(f'''import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationV0
import ToeFormal.Release.BoundedProgramGovernanceControlInstallationResultReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityReviewV0
import ToeFormal.Release.ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0
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

theorem current_authority_tracks_selected_unopened_contract_adjudication :
    currentTarget = "{NEXT_TARGET}" ∧ boundedProgramId = "{PROGRAM_ID}" ∧
    boundedProgramState = "CLOSED" ∧ boundedAttemptNumber = 2 ∧
    Derivation.ToeTargetedCCFTClosureContractExtractionResult.terminalOutcome = "{OUTCOME}" ∧
    Derivation.ToeTargetedCCFTClosureContractExtractionResult.stageThreeAuthorized = false := by
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

theorem stage_one_and_stage_two_authorities_remain_bound :
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityV0.stageOneOpenAuthorized = true ∧
    ToeTargetedCCFTClosureSourceDiscoveryStage1OpenAuthorityReviewV0.accepted = true ∧
    ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityV0.stageTwoOpenAuthorized = true ∧
    ToeTargetedCCFTClosureContractExtractionStage2OpenAuthorityReviewV0.accepted = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''', encoding="utf-8", newline="\n")


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
        validation = {
            "artifact_id": "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_VALIDATION_v0",
            "schema_id": "toe.targeted_ccft_closure.contract_extraction.validation.v0",
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
            "atomic_close_commit_expected_paths": _manifest_stage()["prospective_envelope"]["close_commit_exact_path_set"],
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
            "status": "STAGE_2_ATOMIC_CLOSE_READY_FOR_VALIDATION",
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
    print(close_stage(closed_from_commit=args.closed_from_commit, captured_at_utc=args.captured_at_utc))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
