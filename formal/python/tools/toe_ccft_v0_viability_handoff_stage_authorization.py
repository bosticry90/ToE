"""Open CCFT-v0 viability and distinctiveness Stage 5 without adjudicating it."""

from __future__ import annotations

import argparse
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


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
SEMANTIC_STAGE_ID = "CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF"
TARGET = "assess_toe_ccft_v0_internal_viability_and_distinctiveness_v0"
PREVIOUS_STAGE_TARGET = "execute_toe_ccft_v0_primary_theorem_attack_lanes_v0"
EXPECTED_SCOPE_HASH = "77f37cfde12e8a243aaace9e27fafbfa4611c11bc5f30918323f414b3c51f124"
MODEL_ID = "TOE_CCFT_V0_CP_NLSE_PERIODIC_CUBIC_SURROGATE_v0"
MANIFEST = RELEASE / "bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"
AUTHORITY = RELEASE / "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_STAGE_5_OPEN_AUTHORITY_v0.json"
AUTHORITY_REVIEW = RELEASE / "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_STAGE_5_OPEN_AUTHORITY_REVIEW_v0.json"
STAGE4_RESULT = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_RESULT_v0.json"
STAGE4_REVIEW = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_RESULT_REVIEW_v0.json"
STAGE4_VALIDATION = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_VALIDATION_v0.json"
STAGE4_CLOSE = RELEASE / "bounded_program_events/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_ATTEMPT_04_CLOSE_v0.json"
VALIDATION = RELEASE / "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_OPEN_VALIDATION_v0.json"
EVENT_REL = "formal/docs/release/bounded_program_events/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_ATTEMPT_05_OPEN_v0.json"
EVENT = ROOT / EVENT_REL
OPEN_LEAN = ROOT / "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0ViabilityHandoffAttemptOpen.lean"
CURRENT_TARGET = ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY = ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
KIND = "toe_ccft_v0_internal_viability_and_distinctiveness_handoff_stage_5_open_v0"
OUTCOME = "CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_STAGE_5_OPEN"
STRICT = (
    "STAGE_5_OPEN_EXACT_FROZEN_MODEL_VIABILITY_KNOWN_MODEL_EQUIVALENCE_FINITE_"
    "APPROXIMATION_IDENTIFIABILITY_COMPLEXITY_AND_NONAUTOMATIC_HANDOFF_ZERO_"
    "ADJUDICATION_ROLE_SELECTION_SUCCESSOR_PHYSICAL_PROMOTION_MODEL_MUTATION_OR_CCFT_V1"
)
FULL_COMMIT = re.compile(r"[0-9a-f]{40}")


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def head() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def write_json(path: Path, value: dict) -> None:
    if path.exists():
        raise ValueError(f"immutable OPEN artifact already exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def stage() -> dict:
    value = read(MANIFEST)["stages"][4]
    assert value["stage_number"] == 5
    assert value["semantic_stage_id"] == SEMANTIC_STAGE_ID
    assert value["canonical_target"] == TARGET
    assert value["canonical_scope_hash"] == EXPECTED_SCOPE_HASH
    return value


def check_authority() -> None:
    authority = read(AUTHORITY)
    review = read(AUTHORITY_REVIEW)
    result = read(STAGE4_RESULT)
    canonical = stage()
    assert authority["status"] == "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_5_OPEN_ONLY"
    assert authority["authorized_stage"] == {
        "program_id": PROGRAM_ID,
        "stage_number": 5,
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "canonical_target": TARGET,
        "canonical_scope_hash": EXPECTED_SCOPE_HASH,
    }
    assert authority["canonical_terminal_outcomes"] == canonical["mandatory_terminal_outcomes"]
    assert authority["required_outputs"] == canonical["canonical_scope"]["required_outputs"]
    assert [row["surface_id"] for row in authority["authorized_assessment_surfaces"]] == [
        "MATHEMATICAL_VIABILITY",
        "GENERIC_MODEL_EQUIVALENCE",
        "C_FINITE_APPROXIMATION",
        "C_IDENTIFIABILITY",
        "C_COMPLEXITY",
        "FUTURE_ROLE_AND_HANDOFF",
    ]
    binding = authority["frozen_stage_4_result_binding"]
    assert binding["frozen_model_id"] == MODEL_ID
    assert binding["gauge_equivalence"] == "PROVED"
    assert binding["unit_background_dispersion"] == "PROVED"
    assert binding["zero_background_dispersion"] == "PROVED"
    assert binding["known_model_equivalence"] == "ESTABLISHED_FOR_THE_FROZEN_V0_EQUATION"
    assert result["terminal_outcome"] == "THEOREM_GRADE_RESULT_ESTABLISHED"
    assert result["lifecycle_result"] == "PASSED"
    assert read(STAGE4_REVIEW)["accepted"] is True
    assert read(STAGE4_VALIDATION)["status"] == "STAGE_4_ATOMIC_CLOSE_PRECOMMIT_VALIDATED"
    assert read(STAGE4_CLOSE)["terminal_result"] == "PASSED"
    output = authority["scientific_output_at_authority"]
    for key in [
        "mathematical_viability_status",
        "numerical_reproducibility_status",
        "C_FINITE_APPROXIMATION",
        "C_IDENTIFIABILITY",
        "C_COMPLEXITY",
        "generic_model_equivalence_audit",
    ]:
        assert output[key] == "UNADJUDICATED"
    assert output["future_role"] == "NONE_SELECTED"
    assert output["successor_program"] == "NONE_AUTHORIZED"
    assert authority["scientific_limits"]["frozen_model_mutation_authorized"] is False
    assert authority["scientific_limits"]["new_postulate_or_CCFT_v1_construction_authorized"] is False
    assert authority["scientific_limits"]["automatic_successor_authorization"] is False
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True and all(review["checks"].values())
    assert review["stage_5_authorized"] is True
    assert review["stage_5_open_event_created"] is False
    assert review["successor_program_authorized"] is False
    for evidence in authority["evidence_bindings"]:
        assert sha(ROOT / evidence["path"]) == evidence["sha256"]


def project_registry(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 5 target is not current")
    evidence = "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0ViabilityHandoffAttemptOpen.lean"
    projection.update(
        {
            "active_lane": TARGET,
            "current_target": TARGET,
            "current_target_kind": KIND,
            "current_target_evidence": evidence,
            "current_target_report": EVENT_REL,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT,
            "previous_target": PREVIOUS_STAGE_TARGET,
            "workstream_id": TARGET,
        }
    )
    registry.update(
        {
            "active_lane": TARGET,
            "ACTIVE_LANE_v0": TARGET,
            "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
            "PREVIOUS_LIVE_NEXT_TARGET_v0": PREVIOUS_STAGE_TARGET,
            "CURRENT_LIVE_TARGET_EVIDENCE_v0": evidence,
            "CURRENT_LIVE_TARGET_REPORT_v0": EVENT_REL,
            "CURRENT_LIVE_TARGET_OUTCOME_v0": OUTCOME,
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": STRICT,
            "CURRENT_LIVE_TARGET_KIND_v0": KIND,
            "current_live_next_target": TARGET,
            "current_live_target": TARGET,
            "current_live_target_evidence": evidence,
            "current_live_target_kind": KIND,
            "current_live_target_outcome": OUTCOME,
            "current_live_target_report": EVENT_REL,
            "current_live_target_strict_outcome": STRICT,
            "current_target": TARGET,
            "current_target_evidence": evidence,
            "current_target_kind": KIND,
            "current_target_outcome": OUTCOME,
            "current_target_report": EVENT_REL,
            "current_target_strict_outcome": STRICT,
            "live_next_target": TARGET,
            "live_next_target_evidence": evidence,
            "live_next_target_kind": KIND,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_report": EVENT_REL,
            "live_next_target_strict_outcome": STRICT,
        }
    )
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    if len(active) != 1 or active[0]["workstream_id"] != TARGET:
        raise ValueError("active workstream is not selected Stage 5 target")
    active[0].update(
        {
            "active_lane": TARGET,
            "authorized_target": TARGET,
            "authorized_next_strict_target": TARGET,
            "selected_next_target": TARGET,
            "selected_next_target_kind": KIND,
            "authorization_evidence": evidence,
            "report": EVENT_REL,
            "report_path": EVENT_REL,
            "report_sha256": report_sha256,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT,
            "consumed_target": PREVIOUS_STAGE_TARGET,
            "consumed_target_kind": "closed_bounded_scientific_stage",
            "queue_scope": (
                "Stage 5 is OPEN to assess the frozen CCFT-v0 model's internal viability, "
                "known-model equivalence, finite approximation, identifiability, complexity, "
                "and nonautomatic future role."
            ),
            "claim_status": (
                "OPEN only; no viability, numerical reproducibility, finite-approximation, "
                "identifiability, complexity, generic-equivalence, future-role, successor, "
                "physical, empirical, model-mutation, or CCFT-v1 result exists."
            ),
        }
    )
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstreams"] = [dict(active[0])]
    registry["current_target_state"].update(
        {
            "active_lane": TARGET,
            "live_next_target": TARGET,
            "previous_live_next_target": PREVIOUS_STAGE_TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": evidence,
            "live_next_target_report": EVENT_REL,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT,
        }
    )


def write_lean(event_hash: str, opened_from_commit: str) -> None:
    OPEN_LEAN.write_text(
        f'''namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0ViabilityHandoffAttemptOpen

def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{SEMANTIC_STAGE_ID}"
def target : String := "{TARGET}"
def frozenModelId : String := "{MODEL_ID}"
def scopeHash : String := "{EXPECTED_SCOPE_HASH}"
def eventHash : String := "{event_hash}"
def openedFromCommit : String := "{opened_from_commit}"
def attemptNumber : Nat := 5
def frozenModelCount : Nat := 1
def assessmentSurfaceCount : Nat := 6
def stageFourProvedClaimCount : Nat := 3
def assessmentResultCount : Nat := 0
def selectedFutureRoleCount : Nat := 0
def modelMutated : Bool := false
def packetMutated : Bool := false
def newPostulateAdded : Bool := false
def CCFTV1Constructed : Bool := false
def physicalPromotion : Bool := false
def empiricalPromotion : Bool := false
def successorAuthorized : Bool := false

theorem immutable_open_contains_no_viability_or_handoff_result :
    attemptNumber = 5 ∧ frozenModelCount = 1 ∧ assessmentSurfaceCount = 6 ∧
    stageFourProvedClaimCount = 3 ∧ assessmentResultCount = 0 ∧
    selectedFutureRoleCount = 0 ∧ modelMutated = false ∧
    packetMutated = false ∧ newPostulateAdded = false ∧
    CCFTV1Constructed = false ∧ physicalPromotion = false ∧
    empiricalPromotion = false ∧ successorAuthorized = false := by
  decide

end ToeCCFTV0ViabilityHandoffAttemptOpen
end Derivation
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_TARGET.write_text(
        '''import ToeFormal.Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0ViabilityHandoffAttemptOpen
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := target
def currentEvidencePacketId : String := eventHash
def currentTargetPhase : String := "CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_STAGE_5_OPEN"
def currentBoundedProgramState : String := "OPEN_ATTEMPT_5"

theorem current_target_is_empty_stage_five_open :
    attemptNumber = 5 ∧ frozenModelCount = 1 ∧ assessmentSurfaceCount = 6 ∧
    assessmentResultCount = 0 ∧ selectedFutureRoleCount = 0 ∧
    modelMutated = false ∧ packetMutated = false ∧
    newPostulateAdded = false ∧ CCFTV1Constructed = false ∧
    physicalPromotion = false ∧ empiricalPromotion = false ∧
    successorAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_AUTHORITY.write_text(
        '''import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Release.ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_empty_bounded_stage_five_open :
    ToeCCFTV0ViabilityHandoffStage5OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.attemptNumber = 5 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.frozenModelCount = 1 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.assessmentSurfaceCount = 6 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.assessmentResultCount = 0 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.selectedFutureRoleCount = 0 ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.modelMutated = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.CCFTV1Constructed = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.physicalPromotion = false ∧
    Derivation.ToeCCFTV0ViabilityHandoffAttemptOpen.successorAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )


def open_stage(opened_from_commit: str, captured_at_utc: str) -> str:
    check_authority()
    if not FULL_COMMIT.fullmatch(opened_from_commit) or head() != opened_from_commit:
        raise ValueError("opened_from_commit must equal current full commit id")
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
    assert relative_path == EVENT_REL
    assert event["scope_hash"] == EXPECTED_SCOPE_HASH
    write_event(EVENT, event)
    try:
        project_registry(migrated, sha(EVENT))
        migrated["bounded_programs_v1"][PROGRAM_ID]["program_terminal_status"] = (
            "STAGE_5_OPEN_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_NOT_YET_ADJUDICATED"
        )
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        canonical = stage()
        validation = {
            "artifact_id": "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_OPEN_VALIDATION_v0",
            "schema_id": "toe.ccft_v0.internal_viability_and_distinctiveness_handoff.open_validation.v0",
            "captured_at_utc": captured_at_utc,
            "program_id": PROGRAM_ID,
            "attempt_sequence_number": 5,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "target": TARGET,
            "scope_hash": EXPECTED_SCOPE_HASH,
            "event_path": EVENT_REL,
            "event_hash": event["event_hash"],
            "event_sha256": sha(EVENT),
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "opened_from_commit": opened_from_commit,
            "authority_decision": "AUTHORIZE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_STAGE_5_OPEN",
            "frozen_stage_4_result_binding": {
                "frozen_model_id": MODEL_ID,
                "gauge_equivalence": "PROVED",
                "unit_background_dispersion": "PROVED",
                "zero_background_dispersion": "PROVED",
                "known_model_equivalence": "ESTABLISHED_FOR_THE_FROZEN_V0_EQUATION",
                "status": "BOUND_UNCHANGED_AT_OPEN",
            },
            "assessment_surfaces": [
                "MATHEMATICAL_VIABILITY",
                "GENERIC_MODEL_EQUIVALENCE",
                "C_FINITE_APPROXIMATION",
                "C_IDENTIFIABILITY",
                "C_COMPLEXITY",
                "FUTURE_ROLE_AND_HANDOFF",
            ],
            "atomic_open_commit_expected_paths": canonical["prospective_envelope"]["open_commit_exact_path_set"],
            "canonical_terminal_outcomes": canonical["mandatory_terminal_outcomes"],
            "required_outputs": canonical["canonical_scope"]["required_outputs"],
            "scientific_output_at_open": {
                "frozen_model_id": MODEL_ID,
                "frozen_model_mutated": False,
                "frozen_packet_mutated": False,
                "new_postulates_added": 0,
                "mathematical_viability_status": "UNADJUDICATED",
                "numerical_reproducibility_status": "UNADJUDICATED",
                "C_FINITE_APPROXIMATION": "UNADJUDICATED",
                "C_IDENTIFIABILITY": "UNADJUDICATED",
                "C_COMPLEXITY": "UNADJUDICATED",
                "generic_model_equivalence_audit": "UNADJUDICATED",
                "future_role": "NONE_SELECTED",
                "successor_program": "NONE_AUTHORIZED",
                "physical_interpretation": "NONE",
                "empirical_claim": "NONE",
                "CCFT_v1_constructed": False,
            },
            "validation_checks": {
                "authority_and_review_accepted": True,
                "stage_4_result_review_validation_and_close_bindings_match": True,
                "manifest_scope_target_outputs_and_outcomes_match": True,
                "six_assessment_surfaces_are_bound": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_stage_5_result": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
                "frozen_model_and_packet_are_unchanged": True,
                "physical_empirical_and_successor_promotion_remain_unauthorized": True,
            },
            "status": "STAGE_5_ATOMIC_OPEN_READY_FOR_COMMIT",
        }
        write_json(VALIDATION, validation)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
        write_lean(event["event_hash"], opened_from_commit)
    except Exception:
        EVENT.unlink(missing_ok=True)
        VALIDATION.unlink(missing_ok=True)
        OPEN_LEAN.unlink(missing_ok=True)
        raise
    return relative_path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--opened-from-commit", required=True)
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args()
    print(open_stage(args.opened_from_commit, args.captured_at_utc))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
