"""Open CCFT-v0 theorem-attack Stage 4 without executing a theorem lane."""

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
SEMANTIC_STAGE_ID = "CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION"
TARGET = "execute_toe_ccft_v0_primary_theorem_attack_lanes_v0"
PREVIOUS_STAGE_TARGET = "prepare_toe_ccft_v0_primary_theorem_or_counterexample_packet_v0"
EXPECTED_SCOPE_HASH = "7ff303d25def2c116cf548eaa5c0d3a08438c8c98a4a847323cac38bca0a9e15"
PACKET_ID = "CCFT_V0_GAUGE_EQUIVALENCE_AND_BACKGROUND_RESOLVED_DISPERSION_PACKET_v0"
MODEL_ID = "TOE_CCFT_V0_CP_NLSE_PERIODIC_CUBIC_SURROGATE_v0"
MANIFEST = RELEASE / "bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"
AUTHORITY = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_STAGE_4_OPEN_AUTHORITY_v0.json"
AUTHORITY_REVIEW = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_STAGE_4_OPEN_AUTHORITY_REVIEW_v0.json"
STAGE3_RESULT = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_RESULT_v0.json"
STAGE3_REVIEW = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_RESULT_REVIEW_v0.json"
STAGE3_VALIDATION = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_VALIDATION_v0.json"
STAGE3_CLOSE = RELEASE / "bounded_program_events/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_ATTEMPT_03_CLOSE_v0.json"
VALIDATION = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_OPEN_VALIDATION_v0.json"
EVENT_REL = "formal/docs/release/bounded_program_events/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_ATTEMPT_04_OPEN_v0.json"
EVENT = ROOT / EVENT_REL
OPEN_LEAN = ROOT / "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0PrimaryTheoremAttackAttemptOpen.lean"
CURRENT_TARGET = ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY = ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
KIND = "toe_ccft_v0_primary_theorem_attack_execution_stage_4_open_v0"
OUTCOME = "CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_STAGE_4_OPEN"
STRICT = (
    "STAGE_4_OPEN_EXACT_FROZEN_FOUR_CLAIM_PRIMARY_THEOREM_ATTACK_ZERO_PROOF_"
    "REFUTATION_COUNTEREXAMPLE_SYMBOLIC_NUMERICAL_LEAN_RESULT_MODEL_PACKET_"
    "MUTATION_NEW_POSTULATE_PHYSICAL_PROMOTION_OR_STAGE_5"
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
    value = read(MANIFEST)["stages"][3]
    assert value["stage_number"] == 4
    assert value["semantic_stage_id"] == SEMANTIC_STAGE_ID
    assert value["canonical_target"] == TARGET
    assert value["canonical_scope_hash"] == EXPECTED_SCOPE_HASH
    return value


def check_authority() -> None:
    authority = read(AUTHORITY)
    review = read(AUTHORITY_REVIEW)
    packet = read(STAGE3_RESULT)
    summary = packet["packet_freeze_summary"]
    canonical = stage()
    assert authority["status"] == "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_4_OPEN_ONLY"
    assert authority["authorized_stage"] == {
        "program_id": PROGRAM_ID,
        "stage_number": 4,
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "canonical_target": TARGET,
        "canonical_scope_hash": EXPECTED_SCOPE_HASH,
    }
    assert authority["canonical_terminal_outcomes"] == canonical["mandatory_terminal_outcomes"]
    assert authority["frozen_packet_binding"]["packet_id"] == PACKET_ID
    assert authority["frozen_packet_binding"]["linked_claim_count"] == 4
    assert authority["frozen_packet_binding"]["formal_proposition_count"] == summary["formal_proposition_count"] == 4
    assert authority["frozen_packet_binding"]["formal_negation_count"] == summary["formal_negation_count"] == 4
    assert authority["frozen_model_binding"]["model_id"] == MODEL_ID
    assert packet["terminal_outcome"] == "PRIMARY_THEOREM_PACKET_FROZEN"
    assert packet["lifecycle_result"] == "PASSED"
    assert read(STAGE3_REVIEW)["accepted"] is True
    assert read(STAGE3_VALIDATION)["status"] == "STAGE_3_ATOMIC_CLOSE_PRECOMMIT_VALIDATED"
    assert read(STAGE3_CLOSE)["terminal_result"] == "PASSED"
    output = authority["scientific_output_at_authority"]
    assert output["theorems_proved"] == 0
    assert output["claims_refuted"] == 0
    assert output["counterexamples_found"] == 0
    assert output["gauge_equivalence_result"] == "UNADJUDICATED"
    assert authority["scientific_limits"]["frozen_model_mutation_authorized"] is False
    assert authority["scientific_limits"]["frozen_packet_mutation_authorized"] is False
    assert authority["scientific_limits"]["stage_5_authorized"] is False
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True and all(review["checks"].values())
    assert review["stage_4_authorized"] is True
    assert review["stage_5_authorized"] is False
    for binding in authority["evidence_bindings"]:
        assert sha(ROOT / binding["path"]) == binding["sha256"]


def project_registry(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 4 target is not current")
    evidence = "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0PrimaryTheoremAttackAttemptOpen.lean"
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
        raise ValueError("active workstream is not selected Stage 4 target")
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
                "Stage 4 is OPEN to execute the frozen four-claim CCFT-v0 primary theorem "
                "packet through the bound attack, symbolic, numerical, and faithful Lean lanes."
            ),
            "claim_status": (
                "OPEN only; no proof, refutation, counterexample, symbolic result, numerical "
                "result, Lean theorem proof, historical classification, model or packet "
                "mutation, new postulate, physical promotion, or Stage 5 authority."
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
namespace ToeCCFTV0PrimaryTheoremAttackAttemptOpen

def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{SEMANTIC_STAGE_ID}"
def target : String := "{TARGET}"
def frozenModelId : String := "{MODEL_ID}"
def frozenPacketId : String := "{PACKET_ID}"
def scopeHash : String := "{EXPECTED_SCOPE_HASH}"
def eventHash : String := "{event_hash}"
def openedFromCommit : String := "{opened_from_commit}"
def attemptNumber : Nat := 4
def frozenPacketCount : Nat := 1
def linkedClaimCount : Nat := 4
def formalPropositionCount : Nat := 4
def formalNegationCount : Nat := 4
def executionContractCount : Nat := 3
def theoremResultCount : Nat := 0
def refutedClaimCount : Nat := 0
def counterexampleCount : Nat := 0
def symbolicResultCount : Nat := 0
def numericalResultCount : Nat := 0
def LeanTheoremProofCount : Nat := 0
def modelMutated : Bool := false
def packetMutated : Bool := false
def newPostulateAdded : Bool := false
def historicalFormulaClassified : Bool := false
def physicalPromotion : Bool := false
def stageFiveAuthorized : Bool := false

theorem immutable_open_contains_no_theorem_attack_result :
    attemptNumber = 4 ∧ frozenPacketCount = 1 ∧ linkedClaimCount = 4 ∧
    formalPropositionCount = 4 ∧ formalNegationCount = 4 ∧
    executionContractCount = 3 ∧ theoremResultCount = 0 ∧
    refutedClaimCount = 0 ∧ counterexampleCount = 0 ∧
    symbolicResultCount = 0 ∧ numericalResultCount = 0 ∧
    LeanTheoremProofCount = 0 ∧ modelMutated = false ∧
    packetMutated = false ∧ newPostulateAdded = false ∧
    historicalFormulaClassified = false ∧ physicalPromotion = false ∧
    stageFiveAuthorized = false := by
  decide

end ToeCCFTV0PrimaryTheoremAttackAttemptOpen
end Derivation
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_TARGET.write_text(
        '''import ToeFormal.Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0PrimaryTheoremAttackAttemptOpen
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := target
def currentEvidencePacketId : String := eventHash
def currentTargetPhase : String := "CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_STAGE_4_OPEN"
def currentBoundedProgramState : String := "OPEN_ATTEMPT_4"

theorem current_target_is_empty_stage_four_open :
    attemptNumber = 4 ∧ frozenPacketCount = 1 ∧ linkedClaimCount = 4 ∧
    theoremResultCount = 0 ∧ refutedClaimCount = 0 ∧
    counterexampleCount = 0 ∧ symbolicResultCount = 0 ∧
    numericalResultCount = 0 ∧ LeanTheoremProofCount = 0 ∧
    modelMutated = false ∧ packetMutated = false ∧
    newPostulateAdded = false ∧ historicalFormulaClassified = false ∧
    physicalPromotion = false ∧ stageFiveAuthorized = false := by
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
import ToeFormal.Release.ToeCCFTV0PrimaryTheoremAttackStage4OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_empty_bounded_stage_four_open :
    ToeCCFTV0PrimaryTheoremAttackStage4OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.attemptNumber = 4 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.frozenPacketCount = 1 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.linkedClaimCount = 4 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.theoremResultCount = 0 ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.modelMutated = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.packetMutated = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.physicalPromotion = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremAttackAttemptOpen.stageFiveAuthorized = false := by
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
            "STAGE_4_OPEN_PRIMARY_THEOREM_ATTACK_NOT_YET_ADJUDICATED"
        )
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        canonical = stage()
        validation = {
            "artifact_id": "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_OPEN_VALIDATION_v0",
            "schema_id": "toe.ccft_v0.primary_theorem_attack_execution.open_validation.v0",
            "captured_at_utc": captured_at_utc,
            "program_id": PROGRAM_ID,
            "attempt_sequence_number": 4,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "target": TARGET,
            "scope_hash": EXPECTED_SCOPE_HASH,
            "event_path": EVENT_REL,
            "event_hash": event["event_hash"],
            "event_sha256": sha(EVENT),
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "opened_from_commit": opened_from_commit,
            "authority_decision": "AUTHORIZE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_STAGE_4_OPEN",
            "frozen_packet_binding": {
                "packet_id": PACKET_ID,
                "packet_count": 1,
                "linked_claim_count": 4,
                "formal_proposition_count": 4,
                "formal_negation_count": 4,
                "execution_contract_count": 3,
                "status": "FROZEN_UNCHANGED_AND_UNADJUDICATED_AT_OPEN",
            },
            "atomic_open_commit_expected_paths": canonical["prospective_envelope"]["open_commit_exact_path_set"],
            "canonical_terminal_outcomes": canonical["mandatory_terminal_outcomes"],
            "scientific_output_at_open": {
                "frozen_model_id": MODEL_ID,
                "frozen_model_mutated": False,
                "frozen_packet_mutated": False,
                "new_postulates_added": 0,
                "proofs_completed": 0,
                "claims_refuted": 0,
                "counterexamples_found": 0,
                "symbolic_results_generated": 0,
                "numerical_results_generated": 0,
                "Lean_theorem_proofs_created": 0,
                "gauge_equivalence_result": "UNADJUDICATED",
                "unit_background_dispersion_result": "UNADJUDICATED",
                "zero_background_dispersion_result": "UNADJUDICATED",
                "historical_formula_classification": "UNADJUDICATED",
                "physical_promotion": False,
                "stage_5_output_created": False,
            },
            "validation_checks": {
                "authority_and_review_accepted": True,
                "stage_3_result_review_validation_and_close_bindings_match": True,
                "manifest_scope_target_and_outcomes_match": True,
                "one_packet_four_claim_execution_scope_is_bound": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_mathematical_result": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
                "frozen_model_and_packet_are_unchanged": True,
                "stage_5_remains_unauthorized": True,
            },
            "status": "STAGE_4_ATOMIC_OPEN_READY_FOR_COMMIT",
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
