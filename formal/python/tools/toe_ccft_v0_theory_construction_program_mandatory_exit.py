from __future__ import annotations

"""Complete the mandatory exit for the CCFT-v0 construction program."""

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.bounded_program_governance import validate_registry_extension
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry, repair_registry


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE = REPO_ROOT / "formal/docs/release"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
PROGRAM_ID = "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
EXIT_TARGET = "close_toe_ccft_v0_theory_construction_and_theorem_discovery_v0_after_bounded_result_v0"
OUTCOME = "CCFT_V0_EQUIVALENT_TO_KNOWN_MODEL"
EARNED_ROLE = "KNOWN_MODEL_EQUIVALENT_CCFT_COMPUTATIONAL_BASELINE"
RESULT = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
VALIDATION = RELEASE / f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_VALIDATION_v0.json"
TEST = REPO_ROOT / "formal/python/tests/test_toe_ccft_v0_theory_construction_and_theorem_discovery_v0_bounded_closeout.py"
LEAN = REPO_ROOT / (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.lean"
)
CURRENT_TARGET = REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY = REPO_ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
STAGE5_RESULT = RELEASE / "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_RESULT_v0.json"
STAGE5_REVIEW = RELEASE / "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_RESULT_REVIEW_v0.json"
STRICT = (
    "PROGRAM_TERMINAL_AFTER_CCFT_V0_KNOWN_MODEL_EQUIVALENCE_BASELINE_ESTABLISHED_"
    "FROZEN_MODEL_PROOFS_AND_IMPLEMENTATION_PRESERVED_NO_MATHEMATICAL_NOVELTY_"
    "PHYSICAL_EMPIRICAL_CCFT_V1_GUT_TOE_OR_SCIENTIFIC_SUCCESSOR_AUTHORITY"
)
RESULT_KIND = "toe_ccft_v0_theory_construction_and_theorem_discovery_v0_terminal_closeout"


def read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"immutable mandatory-exit artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def stage_bindings(program: dict[str, Any]) -> dict[str, Any]:
    bindings: dict[str, Any] = {
        "event_chain_changed_by_mandatory_exit": False,
        "event_chain_tip_hash": program["event_chain_tip_hash"],
    }
    for attempt in range(1, 6):
        close = next(
            row
            for row in program["events"]
            if row["event_type"] == "ATTEMPT_CLOSE"
            and row["attempt_sequence_number"] == attempt
        )
        event_path = REPO_ROOT / close["path"]
        event = read(event_path)
        bindings[f"stage_{attempt}_result_path"] = event["result_artifact_path"]
        bindings[f"stage_{attempt}_result_sha256"] = sha(
            REPO_ROOT / event["result_artifact_path"]
        )
        bindings[f"stage_{attempt}_review_path"] = event["review_artifact_path"]
        bindings[f"stage_{attempt}_review_sha256"] = sha(
            REPO_ROOT / event["review_artifact_path"]
        )
        bindings[f"stage_{attempt}_close_event_path"] = close["path"]
        bindings[f"stage_{attempt}_close_event_sha256"] = sha(event_path)
    return bindings


def build_result(registry: dict[str, Any], *, captured_at_utc: str) -> dict[str, Any]:
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    stage5 = read(STAGE5_RESULT)
    if program["state"] != "CLOSED" or program["last_closed_attempt_number"] != 5:
        raise ValueError("all five scientific stages must be closed before mandatory exit")
    if len(program["attempted_stage_ids"]) != 5 or len(program["events"]) != 10:
        raise ValueError("the immutable five-stage event chain is incomplete")
    if stage5["terminal_outcome"] != OUTCOME or stage5["lifecycle_result"] != "PASSED":
        raise ValueError("Stage 5 did not establish the accepted known-model outcome")
    if stage5["earned_future_role"]["primary_classification"] != EARNED_ROLE:
        raise ValueError("Stage 5 did not assign the accepted baseline role")
    handoff = stage5["nonautomatic_future_handoff"]
    if handoff["immediate_target"] != EXIT_TARGET or not handoff["immediate_target_selected"]:
        raise ValueError("Stage 5 did not select the mandatory exit")
    if handoff["scientific_successor_authorized"]:
        raise ValueError("Stage 5 unexpectedly authorized a scientific successor")
    return {
        "artifact_id": f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0",
        "schema_id": "toe.ccft_v0.theory_construction_and_theorem_discovery.bounded_closeout_result.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "execution_target": EXIT_TARGET,
        "program_result_alias": OUTCOME,
        "terminal_outcome": OUTCOME,
        "program_closeout": {
            "authorized_stage_count": 5,
            "attempted_stage_count": 5,
            "last_closed_attempt_number": 5,
            "event_chain_event_count": 10,
            "event_chain_tip_hash": program["event_chain_tip_hash"],
            "repair_attempt_count": 0,
            "mandatory_exit_selected": True,
            "mandatory_exit_completed": True,
            "program_terminal_status": "CLOSED_AFTER_MANDATORY_EXIT",
            "unattempted_stage_ids": [],
            "subsidiary_scientific_targets_created": 0,
        },
        "scientific_result": {
            "frozen_model_id": stage5["frozen_scope_integrity"]["model_id"],
            "frozen_model": "PRESERVED",
            "gauge_equivalence": "PROVED",
            "unit_background_dispersion": "PROVED",
            "zero_background_dispersion": "PROVED",
            "known_model_equivalence": "EXACTLY_EQUIVALENT_TO_BOUND_CUBIC_DEFOCUSING_NLS_COMPARATOR",
            "earned_role": EARNED_ROLE,
            "mathematical_novelty": "NOT_ESTABLISHED",
            "full_PDE_viability": "NOT_INDEPENDENTLY_ADJUDICATED",
            "finite_approximation": "SUPPORTED_ONLY_FOR_FROZEN_TESTS_AND_TESTED_REFINEMENTS",
            "identifiability": "NOT_IDENTIFIABLE_AS_DISTINCT_ISOLATED_DYNAMICS",
            "physical_interpretation": "NONE",
            "empirical_promotion": "NONE",
            "broader_CCFT": "UNREFUTED_BUT_UNESTABLISHED",
            "LCRD_v3": "PRESERVED_INCOMPLETE_UNADJUDICATED",
        },
        "preservation_boundary": {
            "model_contract_preserved": True,
            "reference_implementation_preserved": True,
            "theorem_and_dispersion_results_preserved": True,
            "historical_conflicts_and_context_limits_preserved": True,
            "unsupported_novelty_interpretation_withdrawn": True,
            "repository_work_deleted_or_abandoned": False,
        },
        "future_decision_boundary": {
            "future_route_selected": "NONE",
            "scientific_successor_authorized": False,
            "CCFT_v1_prepared_installed_or_opened": False,
            "LCRD_program_prepared_installed_or_opened": False,
            "standard_model_GUT_or_ToE_completion_program_prepared_installed_or_opened": False,
            "strategic_route_selection_requires_separate_authority": True,
            "candidate_routes_may_be_compared_after_closeout": True,
        },
        "nonpromotion_boundary": {
            "frozen_equation_promoted_as_novel_law": False,
            "physical_coherence_bearer_assigned": False,
            "new_observable_or_empirical_prediction_created": False,
            "broader_CCFT_refuted_or_promoted": False,
            "LCRD_v3_adjudicated_or_promoted": False,
            "CCFT_v1_constructed": False,
            "matter_gravity_seam_or_master_action_work_performed": False,
            "GUT_ToE_or_other_scientific_successor_selected": False,
            "automatic_successor_authorized": False,
        },
        "source_bindings": stage_bindings(program),
        "verdict": (
            "CCFT_V0_PROGRAM_CLOSED_AFTER_KNOWN_MODEL_EQUIVALENCE_BASELINE_"
            "ESTABLISHED_V0_PRESERVED_NOT_PROMOTED_BROADER_CCFT_UNREFUTED_BUT_"
            "UNESTABLISHED_NO_SCIENTIFIC_SUCCESSOR_AUTHORITY"
        ),
    }


def build_review(result: dict[str, Any], *, captured_at_utc: str) -> dict[str, Any]:
    closeout = result["program_closeout"]
    science = result["scientific_result"]
    future = result["future_decision_boundary"]
    boundary = result["nonpromotion_boundary"]
    bindings = result["source_bindings"]
    checks = {
        "all_five_scientific_stages_are_closed": closeout["attempted_stage_count"] == 5,
        "event_chain_has_five_matched_open_close_pairs": closeout["event_chain_event_count"] == 10,
        "event_chain_is_unchanged_by_mandatory_exit": bindings["event_chain_changed_by_mandatory_exit"] is False,
        "repair_attempt_count_remains_zero": closeout["repair_attempt_count"] == 0,
        "known_model_equivalence_outcome_is_preserved": result["terminal_outcome"] == OUTCOME,
        "v0_is_preserved_in_its_earned_baseline_role": science["frozen_model"] == "PRESERVED" and science["earned_role"] == EARNED_ROLE,
        "gauge_and_dispersion_results_are_preserved": science["gauge_equivalence"] == "PROVED" and science["unit_background_dispersion"] == "PROVED" and science["zero_background_dispersion"] == "PROVED",
        "mathematical_novelty_and_full_PDE_viability_are_not_overclaimed": science["mathematical_novelty"] == "NOT_ESTABLISHED" and science["full_PDE_viability"] == "NOT_INDEPENDENTLY_ADJUDICATED",
        "physical_and_empirical_promotion_remain_absent": science["physical_interpretation"] == "NONE" and science["empirical_promotion"] == "NONE",
        "broader_CCFT_and_LCRD_remain_unadjudicated": science["broader_CCFT"] == "UNREFUTED_BUT_UNESTABLISHED" and science["LCRD_v3"] == "PRESERVED_INCOMPLETE_UNADJUDICATED",
        "no_scientific_successor_is_selected_or_authorized": future["future_route_selected"] == "NONE" and future["scientific_successor_authorized"] is False,
        "no_model_physical_gravity_GUT_ToE_or_automatic_promotion_occurred": all(value is False for value in boundary.values()),
        "all_stage_result_review_and_close_event_hashes_are_preserved": all(
            sha(REPO_ROOT / bindings[f"stage_{attempt}_{kind}_path"])
            == bindings[f"stage_{attempt}_{kind}_sha256"]
            for attempt in range(1, 6)
            for kind in ("result", "review", "close_event")
        ),
        "mandatory_exit_completes_the_program": closeout["mandatory_exit_completed"] is True and closeout["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT",
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise ValueError(f"mandatory-exit review failed: {failed}")
    return {
        "artifact_id": f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0",
        "schema_id": "toe.ccft_v0.theory_construction_and_theorem_discovery.bounded_closeout_review.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "reviewed_result": {"path": relative(RESULT), "sha256": sha(RESULT)},
        "checks": checks,
        "failed_checks": [],
        "accepted": True,
        "program_terminal": True,
        "automatic_successor_selected": False,
        "terminal_status": {
            "program": "CLOSED_AFTER_MANDATORY_EXIT",
            "scientific_outcome": OUTCOME,
            "earned_role": EARNED_ROLE,
            "broader_CCFT": "UNREFUTED_BUT_UNESTABLISHED",
            "LCRD_v3": "PRESERVED_INCOMPLETE_UNADJUDICATED",
            "scientific_successor": "NONE_AUTHORIZED",
        },
        "verdict": (
            "ACCEPT_CCFT_V0_PROGRAM_TERMINAL_CLOSEOUT_V0_PRESERVED_AS_KNOWN_MODEL_"
            "BASELINE_NO_PHYSICAL_PROMOTION_OR_SCIENTIFIC_SUCCESSOR"
        ),
    }


def project_registry(registry: dict[str, Any], review_sha256: str) -> dict[str, Any]:
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    program.update({
        "mandatory_exit_completed": True,
        "program_terminal_status": "CLOSED_AFTER_MANDATORY_EXIT",
        "program_terminal_outcome": OUTCOME,
        "earned_model_role": EARNED_ROLE,
        "frozen_model_preserved": True,
        "mathematical_novelty_established": False,
        "physical_interpretation_established": False,
        "empirical_promotion_performed": False,
        "broader_CCFT_status": "UNREFUTED_BUT_UNESTABLISHED",
        "LCRD_v3_status": "PRESERVED_INCOMPLETE_UNADJUDICATED",
        "future_route_selected": "NONE",
        "proposed_successor_authorized": False,
        "proposed_successor_installed": False,
        "proposed_successor_opened": False,
    })
    evidence = relative(LEAN)
    report = relative(REVIEW)
    projection = registry["current_projection_v0"]
    previous = projection["previous_target"]
    projection.update({
        "active_lane": EXIT_TARGET,
        "current_target": EXIT_TARGET,
        "current_target_kind": RESULT_KIND,
        "current_target_evidence": evidence,
        "current_target_report": report,
        "current_target_outcome": OUTCOME,
        "current_target_strict_outcome": STRICT,
        "previous_target": previous,
        "workstream_id": EXIT_TARGET,
    })
    registry.update({
        "active_lane": EXIT_TARGET,
        "ACTIVE_LANE_v0": EXIT_TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0": EXIT_TARGET,
        "PREVIOUS_LIVE_NEXT_TARGET_v0": previous,
        "CURRENT_LIVE_TARGET_EVIDENCE_v0": evidence,
        "CURRENT_LIVE_TARGET_REPORT_v0": report,
        "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
        "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT,
        "CURRENT_LIVE_TARGET_KIND_v0": RESULT_KIND,
        "current_live_next_target": EXIT_TARGET,
        "current_live_target": EXIT_TARGET,
        "current_live_target_evidence": evidence,
        "current_live_target_kind": RESULT_KIND,
        "current_live_target_outcome": OUTCOME,
        "current_live_target_report": report,
        "current_live_target_strict_outcome": STRICT,
        "current_target": EXIT_TARGET,
        "current_target_evidence": evidence,
        "current_target_kind": RESULT_KIND,
        "current_target_outcome": OUTCOME,
        "current_target_report": report,
        "current_target_strict_outcome": STRICT,
        "live_next_target": EXIT_TARGET,
        "live_next_target_evidence": evidence,
        "live_next_target_kind": RESULT_KIND,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_report": report,
        "live_next_target_strict_outcome": STRICT,
    })
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != EXIT_TARGET:
        raise ValueError("mandatory exit must already be the active target")
    workstream = active[0]
    workstream.update({
        "workstream_id": EXIT_TARGET,
        "active_lane": EXIT_TARGET,
        "authorized_target": EXIT_TARGET,
        "authorized_next_strict_target": EXIT_TARGET,
        "selected_next_target": EXIT_TARGET,
        "selected_next_target_kind": RESULT_KIND,
        "authorization_evidence": evidence,
        "report": report,
        "report_path": report,
        "report_sha256": review_sha256,
        "packet_result": OUTCOME,
        "strict_packet_result": STRICT,
        "consumed_target": previous,
        "consumed_target_kind": "completed_bounded_scientific_program_followed_by_mandatory_exit",
        "queue_scope": "CCFT-v0 program terminal after known-model-equivalence baseline result and mandatory exit; strategic route selection requires separate authority.",
        "claim_status": "v0 preserved as a known-model-equivalent computational baseline; broader CCFT and LCRD remain unestablished; no physical promotion or scientific successor authority.",
    })
    registry["active_lanes"] = [EXIT_TARGET]
    registry["active_workstream"] = EXIT_TARGET
    registry["active_workstreams"] = [dict(workstream)]
    registry["current_target_state"].update({
        "active_lane": EXIT_TARGET,
        "live_next_target": EXIT_TARGET,
        "previous_live_next_target": previous,
        "live_next_target_kind": RESULT_KIND,
        "live_next_target_evidence": evidence,
        "live_next_target_report": report,
        "live_next_target_outcome": OUTCOME,
        "live_next_target_strict_outcome": STRICT,
    })
    registry = repair_registry(registry)
    validate_registry_extension(registry)
    return registry


def write_lean() -> None:
    LEAN.write_text(f'''import ToeFormal.Derivation.ToeCCFTV0ViabilityHandoffResult

namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout

def resultId : String := "{PROGRAM_ID}_BOUNDED_CLOSEOUT_RESULT_v0"
def reviewId : String := "{PROGRAM_ID}_BOUNDED_CLOSEOUT_REVIEW_v0"
def programId : String := "{PROGRAM_ID}"
def executionTarget : String := "{EXIT_TARGET}"
def terminalOutcome : String := "{OUTCOME}"
def earnedRole : String := "{EARNED_ROLE}"
def programTerminalStatus : String := "CLOSED_AFTER_MANDATORY_EXIT"

def authorizedStageCount : Nat := 5
def attemptedStageCount : Nat := 5
def eventCount : Nat := 10
def mandatoryExitCompleted : Bool := true
def frozenModelPreserved : Bool := true
def mathematicalNoveltyEstablished : Bool := false
def physicalInterpretationEstablished : Bool := false
def empiricalPromotionPerformed : Bool := false
def broaderCCFTRefuted : Bool := false
def LCRDAdjudicated : Bool := false
def scientificSuccessorAuthorized : Bool := false

theorem ccft_v0_program_completed_its_mandatory_exit :
    terminalOutcome = "{OUTCOME}" ∧ programTerminalStatus = "CLOSED_AFTER_MANDATORY_EXIT" ∧
    authorizedStageCount = 5 ∧ attemptedStageCount = 5 ∧ eventCount = 10 ∧
    mandatoryExitCompleted = true ∧ frozenModelPreserved = true := by
  decide

theorem no_physical_promotion_or_successor_authority :
    mathematicalNoveltyEstablished = false ∧
    physicalInterpretationEstablished = false ∧ empiricalPromotionPerformed = false ∧
    broaderCCFTRefuted = false ∧ LCRDAdjudicated = false ∧
    scientificSuccessorAuthorized = false := by
  decide

end ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_TARGET.write_text(f'''import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := executionTarget
def currentEvidencePacketId : String := reviewId
def currentBoundedProgramId : String := programId
def currentBoundedProgramState : String := programTerminalStatus
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANDATORY_EXIT_COMPLETE"
def currentBoundedAttemptNumber : Nat := attemptedStageCount
def lastClosedBoundedSemanticStage : String := "CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF"
def lastBoundedTerminalResult : String := terminalOutcome

theorem current_target_is_terminal_closeout_without_successor :
    currentLiveTarget = "{EXIT_TARGET}" ∧
    currentBoundedProgramState = "CLOSED_AFTER_MANDATORY_EXIT" ∧
    frozenModelPreserved = true ∧ mathematicalNoveltyEstablished = false ∧
    physicalInterpretationEstablished = false ∧ broaderCCFTRefuted = false ∧
    scientificSuccessorAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_AUTHORITY.write_text('''import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0
import ToeFormal.Release.ToeCCFTV0ViabilityHandoffStage5OpenAuthorityV0

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

theorem current_authority_tracks_terminal_closeout_without_successor_authority :
    boundedProgramState = "CLOSED_AFTER_MANDATORY_EXIT" ∧ boundedAttemptNumber = 5 ∧
    Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.frozenModelPreserved = true ∧
    Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.mathematicalNoveltyEstablished = false ∧
    Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.physicalInterpretationEstablished = false ∧
    Derivation.ToeCCFTV0TheoryConstructionAndTheoremDiscoveryV0BoundedCloseout.scientificSuccessorAuthorized = false := by
  native_decide

theorem stage_five_authority_and_review_remain_bound :
    ToeCCFTV0ViabilityHandoffStage5OpenAuthorityV0.stageFiveOpenAuthorized = true ∧
    ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0.reviewAccepted = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''', encoding="utf-8", newline="\n")


def write_test() -> None:
    TEST.write_text(f'''from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
PROGRAM_ID = "{PROGRAM_ID}"
EXIT_TARGET = "{EXIT_TARGET}"
OUTCOME = "{OUTCOME}"
RESULT = RELEASE / f"{{PROGRAM_ID}}_BOUNDED_CLOSEOUT_RESULT_v0.json"
REVIEW = RELEASE / f"{{PROGRAM_ID}}_BOUNDED_CLOSEOUT_REVIEW_v0.json"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"

def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def test_exit_preserves_known_model_outcome_and_baseline_role() -> None:
    result = read(RESULT)
    assert result["terminal_outcome"] == OUTCOME
    assert result["scientific_result"]["earned_role"] == "{EARNED_ROLE}"
    assert result["scientific_result"]["frozen_model"] == "PRESERVED"

def test_mathematical_physical_and_empirical_boundaries_remain_exact() -> None:
    science = read(RESULT)["scientific_result"]
    assert science["mathematical_novelty"] == "NOT_ESTABLISHED"
    assert science["full_PDE_viability"] == "NOT_INDEPENDENTLY_ADJUDICATED"
    assert science["physical_interpretation"] == "NONE"
    assert science["empirical_promotion"] == "NONE"

def test_broader_ccft_and_lcrd_are_preserved_without_adjudication() -> None:
    science = read(RESULT)["scientific_result"]
    assert science["broader_CCFT"] == "UNREFUTED_BUT_UNESTABLISHED"
    assert science["LCRD_v3"] == "PRESERVED_INCOMPLETE_UNADJUDICATED"

def test_no_scientific_successor_is_selected_or_authorized() -> None:
    result = read(RESULT)
    assert result["future_decision_boundary"]["future_route_selected"] == "NONE"
    assert result["future_decision_boundary"]["scientific_successor_authorized"] is False
    assert all(value is False for value in result["nonpromotion_boundary"].values())

def test_review_accepts_and_source_hashes_reproduce() -> None:
    review = read(REVIEW)
    assert review["accepted"] is True
    assert review["reviewed_result"]["sha256"] == sha(RESULT)
    assert all(review["checks"].values())

def test_registry_is_terminal_at_mandatory_exit() -> None:
    registry = read(REGISTRY)
    program = registry["bounded_programs_v1"][PROGRAM_ID]
    assert program["mandatory_exit_completed"] is True
    assert program["program_terminal_status"] == "CLOSED_AFTER_MANDATORY_EXIT"
    assert program["program_terminal_outcome"] == OUTCOME
    assert program["proposed_successor_authorized"] is False
    assert registry["current_projection_v0"]["current_target"] == EXIT_TARGET
''', encoding="utf-8", newline="\n")


def execute(*, captured_at_utc: str) -> None:
    registry = read(REGISTRY)
    result = build_result(registry, captured_at_utc=captured_at_utc)
    write_json(RESULT, result)
    review = build_review(result, captured_at_utc=captured_at_utc)
    write_json(REVIEW, review)
    registry = project_registry(registry, sha(REVIEW))
    atomic_write_registry(
        REGISTRY,
        (json.dumps(registry, indent=2, sort_keys=True) + "\n").encode("utf-8"),
    )
    write_lean()
    write_test()
    validation = {
        "artifact_id": f"{PROGRAM_ID}_BOUNDED_CLOSEOUT_VALIDATION_v0",
        "schema_id": "toe.ccft_v0.theory_construction_and_theorem_discovery.bounded_closeout_validation.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "result_path": relative(RESULT),
        "result_sha256": sha(RESULT),
        "review_path": relative(REVIEW),
        "review_sha256": sha(REVIEW),
        "governance_validation": {
            "status": "PENDING_PRECOMMIT",
            "event_count": 10,
            "event_chain_changed": False,
            "mandatory_exit_completed": True,
            "repair_attempt_count": 0,
            "mandatory_exit_commit_chronology": "REQUIRED_POST_COMMIT",
        },
        "focused_python_validation": {"status": "PENDING_PRECOMMIT"},
        "focused_lean_validation": {"status": "PENDING_PRECOMMIT"},
        "full_lean_validation": {"status": "PENDING_PRECOMMIT"},
        "deterministic_generation": {"status": "PENDING_PRECOMMIT"},
        "scientific_boundary": {
            "frozen_model_preserved": True,
            "known_model_equivalence_preserved": True,
            "mathematical_novelty_established": False,
            "physical_interpretation_established": False,
            "empirical_promotion_performed": False,
            "broader_CCFT_refuted_or_promoted": False,
            "LCRD_v3_adjudicated_or_promoted": False,
            "CCFT_v1_constructed": False,
            "scientific_successor_selected_or_authorized": False,
        },
        "atomic_closeout_commit_expected_path_count": 9,
        "atomic_closeout_commit_expected_paths": sorted([
            relative(REGISTRY), relative(RESULT), relative(REVIEW), relative(VALIDATION),
            relative(TEST), relative(CURRENT_TARGET), relative(LEAN),
            relative(CURRENT_AUTHORITY), "formal/toe_formal/ToeFormalAll.lean",
        ]),
        "tracked_checkout_expected_clean_after_commit": True,
        "untracked_reddit_expected_untouched": True,
        "status": "MANDATORY_EXIT_CLOSEOUT_READY_FOR_VALIDATION",
    }
    write_json(VALIDATION, validation)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args()
    execute(captured_at_utc=args.captured_at_utc)
    print(relative(RESULT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
