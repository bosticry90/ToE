"""Open CCFT-v0 branch-readiness Stage 1 without selecting a branch."""

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
SEMANTIC_STAGE_ID = "CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION"
TARGET = "select_toe_ccft_v0_branch_after_research_director_decision_v0"
EXPECTED_PREVIOUS_TARGET = (
    "install_toe_ccft_v0_theory_construction_and_theorem_discovery_bounded_program_v0"
)
EXPECTED_SCOPE_HASH = "f23a5be55905604125cb2752cefde7df3f4aa4a6d493aaaea9fcd14559c2c5d4"
MANIFEST = (
    RELEASE
    / "bounded_program_manifests"
    / "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"
)
AUTHORITY = (
    RELEASE
    / "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_STAGE_1_OPEN_AUTHORITY_v0.json"
)
AUTHORITY_REVIEW = (
    RELEASE
    / "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_STAGE_1_OPEN_AUTHORITY_REVIEW_v0.json"
)
VALIDATION = (
    RELEASE
    / "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_OPEN_VALIDATION_v0.json"
)
EVENT_REL = (
    "formal/docs/release/bounded_program_events/"
    "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_"
    "ATTEMPT_01_OPEN_v0.json"
)
EVENT = ROOT / EVENT_REL
OPEN_LEAN = (
    ROOT
    / "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0BranchReadinessAttemptOpen.lean"
)
CURRENT_TARGET = ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY = ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
KIND = "toe_ccft_v0_research_director_branch_readiness_stage_1_open_v0"
OUTCOME = "CCFT_V0_BRANCH_READINESS_STAGE_1_OPEN"
STRICT = (
    "STAGE_1_OPEN_NO_BRANCH_SELECTION_EQUATION_REPAIR_POSTULATE_MODEL_FREEZE_"
    "THEOREM_PACKET_THEOREM_EXECUTION_PHYSICAL_PROMOTION_OR_STAGE_2"
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
    value = read(MANIFEST)["stages"][0]
    assert value["stage_number"] == 1
    assert value["semantic_stage_id"] == SEMANTIC_STAGE_ID
    assert value["canonical_target"] == TARGET
    assert value["canonical_scope_hash"] == EXPECTED_SCOPE_HASH
    return value


def check_authority() -> None:
    authority = read(AUTHORITY)
    review = read(AUTHORITY_REVIEW)
    canonical = stage()
    assert authority["status"] == "SCIENTIFIC_AUTHORITY_GRANTED_FOR_ATOMIC_STAGE_1_OPEN_ONLY"
    assert authority["authorized_stage"] == {
        "program_id": PROGRAM_ID,
        "stage_number": 1,
        "semantic_stage_id": SEMANTIC_STAGE_ID,
        "canonical_target": TARGET,
        "canonical_scope_hash": EXPECTED_SCOPE_HASH,
    }
    assert authority["canonical_terminal_outcomes"] == canonical["mandatory_terminal_outcomes"]
    assert authority["blocking_outcomes"] == read(MANIFEST)["stage_1_blocking_outcomes"]
    assert authority["scientific_output_at_authority"]["branch_selected"] == "NONE"
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True and all(review["checks"].values())
    assert review["stage_2_authorized"] is False
    for binding in authority["evidence_bindings"]:
        assert sha(ROOT / binding["path"]) == binding["sha256"]


def project_registry(registry: dict, report_sha256: str) -> None:
    projection = registry["current_projection_v0"]
    if projection["current_target"] != EXPECTED_PREVIOUS_TARGET:
        raise ValueError("CCFT-v0 installed-unopened target is not current")
    projection.update(
        {
            "active_lane": TARGET,
            "current_target": TARGET,
            "current_target_kind": KIND,
            "current_target_evidence": (
                "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0BranchReadinessAttemptOpen.lean"
            ),
            "current_target_report": EVENT_REL,
            "current_target_outcome": OUTCOME,
            "current_target_strict_outcome": STRICT,
            "previous_target": EXPECTED_PREVIOUS_TARGET,
            "workstream_id": TARGET,
        }
    )
    evidence = projection["current_target_evidence"]
    registry.update(
        {
            "active_lane": TARGET,
            "ACTIVE_LANE_v0": TARGET,
            "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
            "PREVIOUS_LIVE_NEXT_TARGET_v0": EXPECTED_PREVIOUS_TARGET,
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
    if len(active) != 1 or active[0]["workstream_id"] != EXPECTED_PREVIOUS_TARGET:
        raise ValueError("active workstream does not match unopened installation target")
    active[0].update(
        {
            "workstream_id": TARGET,
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
            "consumed_target": EXPECTED_PREVIOUS_TARGET,
            "consumed_target_kind": "installed_unopened_program_checkpoint",
            "queue_scope": (
                "Stage 1 is OPEN for the four-option Research Director branch decision; "
                "no comparison result or branch selection exists at OPEN."
            ),
            "claim_status": (
                "OPEN only; branch, equation, postulate, model, theorem packet, theorem "
                "result, physical interpretation, and Stage 2 authority remain none."
            ),
        }
    )
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstreams"] = [dict(active[0])]
    if TARGET not in registry["next_strict_target_coverage"]:
        registry["next_strict_target_coverage"].append(TARGET)
        registry["next_strict_target_coverage"].sort()
    registry["current_target_state"].update(
        {
            "active_lane": TARGET,
            "live_next_target": TARGET,
            "previous_live_next_target": EXPECTED_PREVIOUS_TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": evidence,
            "live_next_target_report": EVENT_REL,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT,
        }
    )


def write_lean_surfaces(event_hash: str, opened_from_commit: str) -> None:
    OPEN_LEAN.write_text(
        f'''namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0BranchReadinessAttemptOpen

def programId : String := "{PROGRAM_ID}"
def semanticStageId : String := "{SEMANTIC_STAGE_ID}"
def target : String := "{TARGET}"
def scopeHash : String := "{EXPECTED_SCOPE_HASH}"
def eventHash : String := "{event_hash}"
def openedFromCommit : String := "{opened_from_commit}"
def attemptNumber : Nat := 1
def canonicalOutcomeCount : Nat := 4
def blockingOutcomeCount : Nat := 2
def branchSelected : Bool := false
def modelConstructed : Bool := false
def postulateCreated : Bool := false
def theoremPacketPrepared : Bool := false
def theoremAttempted : Bool := false
def stageTwoAuthorized : Bool := false

theorem immutable_open_contains_no_scientific_decision :
    attemptNumber = 1 ∧ canonicalOutcomeCount = 4 ∧ blockingOutcomeCount = 2 ∧
    branchSelected = false ∧ modelConstructed = false ∧ postulateCreated = false ∧
    theoremPacketPrepared = false ∧ theoremAttempted = false ∧
    stageTwoAuthorized = false := by
  decide

end ToeCCFTV0BranchReadinessAttemptOpen
end Derivation
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_TARGET.write_text(
        '''import ToeFormal.Derivation.ToeCCFTV0BranchReadinessAttemptOpen

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0BranchReadinessAttemptOpen
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := target
def currentEvidencePacketId : String := eventHash
def currentTargetPhase : String := "CCFT_V0_BRANCH_READINESS_STAGE_1_OPEN"
def currentBoundedProgramState : String := "OPEN_ATTEMPT_1"

theorem current_target_is_nonselecting_stage_one_open :
    attemptNumber = 1 ∧ branchSelected = false ∧ modelConstructed = false ∧
    postulateCreated = false ∧ theoremPacketPrepared = false ∧
    theoremAttempted = false ∧ stageTwoAuthorized = false := by
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
import ToeFormal.Release.ToeCCFTV0BranchReadinessStage1OpenAuthorityReviewV0

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_valid_nonselecting_open :
    ToeCCFTV0BranchReadinessStage1OpenAuthorityReviewV0.reviewAccepted = true ∧
    Derivation.ToeCCFTV0BranchReadinessAttemptOpen.attemptNumber = 1 ∧
    Derivation.ToeCCFTV0BranchReadinessAttemptOpen.branchSelected = false ∧
    Derivation.ToeCCFTV0BranchReadinessAttemptOpen.modelConstructed = false ∧
    Derivation.ToeCCFTV0BranchReadinessAttemptOpen.stageTwoAuthorized = false := by
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
        raise ValueError("opened_from_commit must equal the current full commit id")
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
        migrated = repair_registry(migrated)
        validate_registry_extension(migrated)
        canonical = stage()
        validation = {
            "artifact_id": "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION_OPEN_VALIDATION_v0",
            "schema_id": "toe.ccft_v0.research_director_branch_readiness_decision.open_validation.v0",
            "captured_at_utc": captured_at_utc,
            "program_id": PROGRAM_ID,
            "attempt_sequence_number": 1,
            "semantic_stage_id": SEMANTIC_STAGE_ID,
            "target": TARGET,
            "scope_hash": EXPECTED_SCOPE_HASH,
            "event_path": EVENT_REL,
            "event_hash": event["event_hash"],
            "event_sha256": sha(EVENT),
            "registry_snapshot_hash": event["registry_snapshot_hash"],
            "opened_from_commit": opened_from_commit,
            "authority_decision": "AUTHORIZE_CCFT_V0_BRANCH_SELECTION_STAGE_1_OPEN",
            "atomic_open_commit_expected_paths": canonical["prospective_envelope"]["open_commit_exact_path_set"],
            "canonical_terminal_outcomes": canonical["mandatory_terminal_outcomes"],
            "blocking_outcomes": read(MANIFEST)["stage_1_blocking_outcomes"],
            "scientific_output_at_open": {
                "director_comparison_performed": False,
                "branch_selected": "NONE",
                "equation_selected_or_repaired": False,
                "new_postulates": 0,
                "model_frozen": False,
                "theorem_packet_prepared": False,
                "theorem_attempted": False,
                "stage_2_output_created": False,
            },
            "validation_checks": {
                "authority_and_review_accepted": True,
                "manifest_scope_and_target_match": True,
                "event_and_registry_projection_match": True,
                "blocking_lifecycle_is_frozen": True,
                "open_checkpoint_contains_no_scientific_result": True,
                "program_state_is_open": migrated["bounded_programs_v1"][PROGRAM_ID]["state"] == "OPEN",
                "stage_2_remains_unauthorized": True,
            },
            "status": "STAGE_1_ATOMIC_OPEN_READY_FOR_COMMIT",
        }
        write_json(VALIDATION, validation)
        atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(migrated))
        write_lean_surfaces(event["event_hash"], opened_from_commit)
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
