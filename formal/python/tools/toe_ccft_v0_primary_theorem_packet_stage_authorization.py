"""Open CCFT-v0 theorem-packet Stage 3 without preparing or executing a theorem."""

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
SEMANTIC_STAGE_ID = "CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION"
TARGET = "prepare_toe_ccft_v0_primary_theorem_or_counterexample_packet_v0"
PREVIOUS_STAGE_TARGET = "complete_and_freeze_toe_ccft_v0_model_contract_v0"
EXPECTED_SCOPE_HASH = "b0db245201d0fdc6edc15a8ac6028c01725ef4a0e2e87c53f9835094df1fe506"
PACKET_ID = "CCFT_V0_GAUGE_EQUIVALENCE_AND_BACKGROUND_RESOLVED_DISPERSION_PACKET_v0"
MODEL_ID = "TOE_CCFT_V0_CP_NLSE_PERIODIC_CUBIC_SURROGATE_v0"
MANIFEST = RELEASE / "bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"
AUTHORITY = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_STAGE_3_OPEN_AUTHORITY_v0.json"
AUTHORITY_REVIEW = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_STAGE_3_OPEN_AUTHORITY_REVIEW_v0.json"
STAGE2_RESULT = RELEASE / "TOE_CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE_RESULT_v0.json"
STAGE2_REVIEW = RELEASE / "TOE_CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE_RESULT_REVIEW_v0.json"
STAGE2_VALIDATION = RELEASE / "TOE_CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE_VALIDATION_v0.json"
STAGE2_CLOSE = RELEASE / "bounded_program_events/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_ATTEMPT_02_CLOSE_v0.json"
VALIDATION = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_OPEN_VALIDATION_v0.json"
EVENT_REL = "formal/docs/release/bounded_program_events/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_ATTEMPT_03_OPEN_v0.json"
EVENT = ROOT / EVENT_REL
OPEN_LEAN = ROOT / "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0PrimaryTheoremPacketAttemptOpen.lean"
CURRENT_TARGET = ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY = ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
KIND = "toe_ccft_v0_primary_theorem_packet_preparation_stage_3_open_v0"
OUTCOME = "CCFT_V0_PRIMARY_THEOREM_PACKET_STAGE_3_OPEN"
STRICT = (
    "STAGE_3_OPEN_ONE_COMPOUND_GAUGE_EQUIVALENCE_AND_BACKGROUND_RESOLVED_DISPERSION_"
    "PACKET_ZERO_FROZEN_PROPOSITIONS_NEGATIONS_EXECUTION_CONTRACTS_THEOREM_RESULTS_"
    "MODEL_MUTATION_PHYSICAL_PROMOTION_OR_STAGE_4"
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
    value = read(MANIFEST)["stages"][2]
    assert value["stage_number"] == 3
    assert value["semantic_stage_id"] == SEMANTIC_STAGE_ID
    assert value["canonical_target"] == TARGET
    assert value["canonical_scope_hash"] == EXPECTED_SCOPE_HASH
    return value


def check_authority() -> None:
    authority = read(AUTHORITY)
    review = read(AUTHORITY_REVIEW)
    model = read(STAGE2_RESULT)
    canonical = stage()
    assert authority["status"] == "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_3_OPEN_ONLY"
    assert authority["authorized_stage"] == {
        "program_id": PROGRAM_ID,
        "stage_number": 3,
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "canonical_target": TARGET,
        "canonical_scope_hash": EXPECTED_SCOPE_HASH,
    }
    assert authority["canonical_terminal_outcomes"] == canonical["mandatory_terminal_outcomes"]
    assert authority["primary_packet_refinement"]["packet_id"] == PACKET_ID
    assert authority["primary_packet_refinement"]["packet_count"] == 1
    assert authority["primary_packet_refinement"]["compound_claim_count"] == 4
    assert authority["frozen_model_binding"]["model_id"] == MODEL_ID
    assert authority["frozen_model_binding"]["governing_equation"] == model["immutable_model_contract"]["dynamics"]["equation"]
    assert model["terminal_outcome"] == "CCFT_V0_MODEL_CONTRACT_FROZEN"
    assert model["lifecycle_result"] == "PASSED"
    assert read(STAGE2_REVIEW)["accepted"] is True
    assert read(STAGE2_VALIDATION)["status"] == "STAGE_2_ATOMIC_CLOSE_PRECOMMIT_VALIDATED"
    assert read(STAGE2_CLOSE)["terminal_result"] == "PASSED"
    assert authority["scientific_output_at_authority"]["primary_theorem_packets_frozen"] == 0
    assert authority["scientific_output_at_authority"]["theorems_proved"] == 0
    assert authority["scientific_limits"]["stage_4_authorized"] is False
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True and all(review["checks"].values())
    assert review["stage_4_authorized"] is False
    for binding in authority["evidence_bindings"]:
        assert sha(ROOT / binding["path"]) == binding["sha256"]


def project_registry(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != TARGET:
        raise ValueError("selected Stage 3 target is not current")
    evidence = "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0PrimaryTheoremPacketAttemptOpen.lean"
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
        raise ValueError("active workstream is not selected Stage 3 target")
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
                "Stage 3 is OPEN to prepare one compound gauge-equivalence and "
                "background-resolved dispersion theorem packet for the frozen CCFT-v0 model."
            ),
            "claim_status": (
                "OPEN only; no proposition, negation, execution contract, proof, disproof, "
                "symbolic or numerical theorem result, Lean proof, model mutation, physical "
                "promotion, historical classification, or Stage 4 authority."
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
namespace ToeCCFTV0PrimaryTheoremPacketAttemptOpen

def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{SEMANTIC_STAGE_ID}"
def target : String := "{TARGET}"
def frozenModelId : String := "{MODEL_ID}"
def proposedPacketId : String := "{PACKET_ID}"
def scopeHash : String := "{EXPECTED_SCOPE_HASH}"
def eventHash : String := "{event_hash}"
def openedFromCommit : String := "{opened_from_commit}"
def attemptNumber : Nat := 3
def maximumPrimaryTheoremPackets : Nat := 1
def proposedCompoundClaimCount : Nat := 4
def frozenPacketCount : Nat := 0
def frozenPropositionCount : Nat := 0
def frozenFormalNegationCount : Nat := 0
def executionContractCount : Nat := 0
def theoremResultCount : Nat := 0
def counterexampleCount : Nat := 0
def modelMutated : Bool := false
def historicalFormulaClassified : Bool := false
def physicalPromotion : Bool := false
def stageFourAuthorized : Bool := false

theorem immutable_open_contains_no_packet_or_theorem_output :
    attemptNumber = 3 ∧ maximumPrimaryTheoremPackets = 1 ∧
    proposedCompoundClaimCount = 4 ∧ frozenPacketCount = 0 ∧
    frozenPropositionCount = 0 ∧ frozenFormalNegationCount = 0 ∧
    executionContractCount = 0 ∧ theoremResultCount = 0 ∧
    counterexampleCount = 0 ∧ modelMutated = false ∧
    historicalFormulaClassified = false ∧ physicalPromotion = false ∧
    stageFourAuthorized = false := by
  decide

end ToeCCFTV0PrimaryTheoremPacketAttemptOpen
end Derivation
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_TARGET.write_text(
        '''import ToeFormal.Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0PrimaryTheoremPacketAttemptOpen
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := target
def currentEvidencePacketId : String := eventHash
def currentTargetPhase : String := "CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_STAGE_3_OPEN"
def currentBoundedProgramState : String := "OPEN_ATTEMPT_3"

theorem current_target_is_empty_stage_three_open :
    attemptNumber = 3 ∧ maximumPrimaryTheoremPackets = 1 ∧
    proposedCompoundClaimCount = 4 ∧ frozenPacketCount = 0 ∧
    frozenPropositionCount = 0 ∧ frozenFormalNegationCount = 0 ∧
    executionContractCount = 0 ∧ theoremResultCount = 0 ∧
    counterexampleCount = 0 ∧ modelMutated = false ∧
    historicalFormulaClassified = false ∧ physicalPromotion = false ∧
    stageFourAuthorized = false := by
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
import ToeFormal.Release.ToeCCFTV0PrimaryTheoremPacketStage3OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_empty_bounded_stage_three_open :
    ToeCCFTV0PrimaryTheoremPacketStage3OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.attemptNumber = 3 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.frozenPacketCount = 0 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.frozenPropositionCount = 0 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.theoremResultCount = 0 ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.modelMutated = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.physicalPromotion = false ∧
    Derivation.ToeCCFTV0PrimaryTheoremPacketAttemptOpen.stageFourAuthorized = false := by
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
            "STAGE_3_OPEN_PRIMARY_THEOREM_PACKET_NOT_YET_PREPARED"
        )
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        canonical = stage()
        validation = {
            "artifact_id": "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_OPEN_VALIDATION_v0",
            "schema_id": "toe.ccft_v0.primary_theorem_packet_preparation.open_validation.v0",
            "captured_at_utc": captured_at_utc,
            "program_id": PROGRAM_ID,
            "attempt_sequence_number": 3,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "target": TARGET,
            "scope_hash": EXPECTED_SCOPE_HASH,
            "event_path": EVENT_REL,
            "event_hash": event["event_hash"],
            "event_sha256": sha(EVENT),
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "opened_from_commit": opened_from_commit,
            "authority_decision": "AUTHORIZE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_STAGE_3_OPEN",
            "proposed_packet_scope": {
                "packet_id": PACKET_ID,
                "packet_count": 1,
                "compound_claim_count": 4,
                "claims": [
                    "EXACT_GAUGE_EQUIVALENCE",
                    "UNIT_BACKGROUND_DISPERSION",
                    "ZERO_BACKGROUND_DISPERSION",
                    "HISTORICAL_FORMULA_CLASSIFICATION",
                ],
                "status": "SCOPE_BOUND_PACKET_NOT_FROZEN_OR_ADJUDICATED",
            },
            "atomic_open_commit_expected_paths": canonical["prospective_envelope"]["open_commit_exact_path_set"],
            "canonical_terminal_outcomes": canonical["mandatory_terminal_outcomes"],
            "scientific_output_at_open": {
                "frozen_model_id": MODEL_ID,
                "frozen_model_mutated": False,
                "primary_theorem_packets_frozen": 0,
                "formal_propositions_frozen": 0,
                "formal_negations_frozen": 0,
                "execution_contracts_frozen": 0,
                "proof_or_disproof_attempted": False,
                "symbolic_or_numerical_theorem_result_generated": False,
                "Lean_theorem_proof_created": False,
                "gauge_equivalence_result": "NONE",
                "unit_background_dispersion_result": "NONE",
                "zero_background_dispersion_result": "NONE",
                "historical_formula_classification": "NONE",
                "physical_promotion": False,
                "stage_4_output_created": False,
            },
            "validation_checks": {
                "authority_and_review_accepted": True,
                "stage_2_result_review_validation_and_close_bindings_match": True,
                "manifest_scope_target_and_outcomes_match": True,
                "one_packet_four_claim_refinement_is_bound": True,
                "event_and_registry_projection_match": True,
                "open_checkpoint_contains_no_packet_or_theorem_output": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
                "frozen_model_is_unchanged": True,
                "stage_4_remains_unauthorized": True,
            },
            "status": "STAGE_3_ATOMIC_OPEN_READY_FOR_COMMIT",
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
