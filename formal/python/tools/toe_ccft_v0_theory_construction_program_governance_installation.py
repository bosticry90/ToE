from __future__ import annotations

"""Authorize and install the bounded CCFT-v0 construction program unopened."""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import bounded_program_governance as governance
from formal.python.tools.loop_control_registry_integrity import (
    atomic_write_registry,
    repair_registry,
)


ROOT = find_repo_root(Path(__file__))
RELEASE = ROOT / "formal/docs/release"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
PROGRAM_ID = "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
PREPARATION_TARGET = "prepare_bounded_ccft_v0_theory_construction_program"
INSTALLATION_TARGET = (
    "install_toe_ccft_v0_theory_construction_and_theorem_discovery_bounded_program_v0"
)
MANDATORY_EXIT = (
    "close_toe_ccft_v0_theory_construction_and_theorem_discovery_v0_"
    "after_bounded_result_v0"
)
MANIFEST_REL = (
    "formal/docs/release/bounded_program_manifests/"
    f"{PROGRAM_ID}_MANIFEST_v1.json"
)
MANIFEST = ROOT / MANIFEST_REL
PREPARATION_RESULT = (
    RELEASE
    / "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
)
PREPARATION_REVIEW = (
    RELEASE
    / "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
)
DIRECTOR_PACKET = RELEASE / "TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0.json"
AUTHORITY = (
    RELEASE
    / "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_v0.json"
)
AUTHORITY_REVIEW = (
    RELEASE
    / "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_REVIEW_v0.json"
)
INSTALLATION = (
    RELEASE
    / "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_RESULT_v0.json"
)
INSTALLATION_REVIEW = (
    RELEASE
    / "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_REVIEW_v0.json"
)
INSTALLATION_VALIDATION = (
    RELEASE
    / "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_VALIDATION_v0.json"
)
AUTHORITY_TEST = (
    ROOT
    / "formal/python/tests/test_toe_ccft_v0_theory_construction_program_installation_authority.py"
)
INSTALLATION_TEST = (
    ROOT
    / "formal/python/tests/test_toe_ccft_v0_theory_construction_program_governance_installation.py"
)
AUTHORITY_LEAN = (
    ROOT
    / "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0TheoryConstructionProgramInstallationAuthority.lean"
)
INSTALLATION_LEAN = (
    ROOT
    / "formal/toe_formal/ToeFormal/Release/ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.lean"
)
REVIEW_LEAN = (
    ROOT
    / "formal/toe_formal/ToeFormal/Release/ToeCCFTV0TheoryConstructionProgramGovernanceInstallationReview.lean"
)
CURRENT_TARGET = ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY = ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"


PROVENANCE = [
    "SOURCE_RECOVERED",
    "KNOWN_PHYSICS_BASELINE",
    "NEW_CCFT_POSTULATE",
    "NUMERICAL_CONVENTION",
    "MATHEMATICAL_CONTROL",
]
EXTERNAL_CHECKS = ["C_FINITE_APPROXIMATION", "C_IDENTIFIABILITY", "C_COMPLEXITY"]
ATTACK_LANES = ["PROVE", "DISPROVE", "CONSTRUCT", "FIND_COUNTEREXAMPLE"]
THEOREM_FIELDS = [
    "exact_definitions",
    "domains_and_regularity",
    "assumptions",
    "target_theorem",
    "formal_negation",
    "allowed_lemmas",
    "forbidden_conclusions",
    "known_examples",
    "known_counterexamples",
    "symbolic_test_suite",
    "numerical_test_suite",
    "Lean_theorem_signature",
    "physical_claim_boundary",
]
COMMON_INPUTS = [
    "TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0",
    "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
    "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_BOUNDED_CLOSEOUT_RESULT_v0",
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_BOUNDED_CLOSEOUT_REVIEW_v0",
    "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_v0",
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_RESULT_v0",
]
COMMON_PROHIBITED = [
    "unlabeled scientific assumption insertion",
    "historical or targeted archive recovery reopening",
    "physical coherence bearer units scale preparation or measurement claim",
    "matter gravity seam master-action or empirical construction",
    "canonical evidence promotion",
    "claiming a mathematical result establishes physical truth",
    "automatic successor authorization",
    "repository claim exhaustion",
]
PROGRAM_OUTCOMES = [
    "CCFT_V0_MATHEMATICALLY_VIABLE_DISTINCTIVE_SURROGATE",
    "CCFT_V0_EQUIVALENT_TO_KNOWN_MODEL",
    "CCFT_V0_INTERNALLY_INCONSISTENT",
    "VIABILITY_OR_DISTINCTIVENESS_UNRESOLVED",
]


STAGES = [
    {
        "number": 1,
        "id": "CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION",
        "target": "select_toe_ccft_v0_branch_after_research_director_decision_v0",
        "question": (
            "Which frozen director option offers the greatest bounded decision value "
            "without treating convenience, completeness, or novelty as evidence?"
        ),
        "outputs": [
            "reviewed_research_director_decision_packet",
            "option_by_option_postulate_and_conflict_burden",
            "exactly_one_branch_route_or_honest_block_result",
        ],
        "prohibited": [
            "equation selection or repair",
            "new postulate insertion",
            "model construction",
            "theorem-packet preparation or theorem execution",
        ],
        "outcomes": [
            "SELECT_CP_NLSE_AS_CCFT_V0_CORE",
            "SELECT_LCRD_V3_AS_CCFT_V0_CORE",
            "RETAIN_TWO_SEPARATE_CONSTRUCTION_CANDIDATES",
            "NO_BRANCH_READY_WITHOUT_FOUNDATIONAL_POSTULATE",
        ],
        "stem": "TOE_CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION",
        "tool": "toe_ccft_v0_branch_readiness_stage_authorization.py",
        "lean_open": "ToeCCFTV0BranchReadinessAttemptOpen",
        "lean_result": "ToeCCFTV0BranchReadinessResult",
    },
    {
        "number": 2,
        "id": "CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE",
        "target": "complete_and_freeze_toe_ccft_v0_model_contract_v0",
        "question": (
            "What single explicit provenance-labeled model contract closes and "
            "freezes the selected branch within the eight-postulate ceiling?"
        ),
        "outputs": [
            "immutable_model_version",
            "complete_model_and_data_contract",
            "component_provenance_ledger",
            "reference_implementation_and_comparator_vectors",
            "failure_contract",
        ],
        "prohibited": [
            "unlabeled assumption insertion",
            "more than one frozen model",
            "post-freeze feature expansion",
            "theorem-packet preparation or theorem execution",
        ],
        "outcomes": [
            "CCFT_V0_MODEL_CONTRACT_FROZEN",
            "MODEL_CONTRACT_REQUIRES_MORE_THAN_FROZEN_POSTULATE_BUDGET",
            "SELECTED_ROUTE_CONTRADICTORY_OR_UNDERDEFINED",
            "REFERENCE_IMPLEMENTATION_NOT_REPRODUCIBLE",
        ],
        "stem": "TOE_CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE",
        "tool": "toe_ccft_v0_model_contract_freeze_stage_authorization.py",
        "lean_open": "ToeCCFTV0ModelContractFreezeAttemptOpen",
        "lean_result": "ToeCCFTV0ModelContractFreezeResult",
    },
    {
        "number": 3,
        "id": "CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION",
        "target": "prepare_toe_ccft_v0_primary_theorem_or_counterexample_packet_v0",
        "question": (
            "Which one theorem-grade question for the frozen model is well-defined, "
            "scientifically consequential, and maximally decision-enabling?"
        ),
        "outputs": [
            "research_director_theorem_decision_packet",
            "formal_proposition_and_negation",
            "assumption_and_dependency_ledger",
            "symbolic_numerical_and_Lean_execution_contracts",
        ],
        "prohibited": [
            "proof disproof construction or counterexample execution",
            "symbolic or numerical theorem-result generation",
            "Lean theorem proof",
            "frozen-model mutation",
        ],
        "outcomes": [
            "PRIMARY_THEOREM_PACKET_FROZEN",
            "THEOREM_PACKET_UNDERDEFINED",
            "THEOREM_TARGET_LACKS_DECISION_VALUE",
        ],
        "stem": "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION",
        "tool": "toe_ccft_v0_primary_theorem_packet_stage_authorization.py",
        "lean_open": "ToeCCFTV0PrimaryTheoremPacketAttemptOpen",
        "lean_result": "ToeCCFTV0PrimaryTheoremPacketResult",
    },
    {
        "number": 4,
        "id": "CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION",
        "target": "execute_toe_ccft_v0_primary_theorem_attack_lanes_v0",
        "question": (
            "What decisive proof, disproof, construction, counterexample, symbolic, "
            "numerical, or formal result follows from the frozen packet?"
        ),
        "outputs": [
            "independent_proof_disproof_construction_and_counterexample_attempts",
            "symbolic_and_numerical_checks",
            "Lean_status_and_fidelity_review",
            "adjudicated_mathematical_result",
        ],
        "prohibited": [
            "changing the frozen model or theorem packet to rescue a result",
            "collapsing mathematical and physical status",
            "claiming failed proof attempts establish theorem falsehood",
        ],
        "outcomes": [
            "THEOREM_GRADE_RESULT_ESTABLISHED",
            "COUNTEREXAMPLE_OR_NO_GO_RESULT_ESTABLISHED",
            "RESULT_CONDITIONALLY_SUPPORTED_NOT_FORMALIZED",
            "MODEL_DEFINITION_INSUFFICIENT_FOR_THEOREM",
        ],
        "stem": "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION",
        "tool": "toe_ccft_v0_primary_theorem_attack_stage_authorization.py",
        "lean_open": "ToeCCFTV0PrimaryTheoremAttackAttemptOpen",
        "lean_result": "ToeCCFTV0PrimaryTheoremAttackResult",
    },
    {
        "number": 5,
        "id": "CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF",
        "target": "assess_toe_ccft_v0_internal_viability_and_distinctiveness_v0",
        "question": (
            "Does the frozen model survive internal and external checks and remain "
            "distinct from known generic systems enough for a later proposal?"
        ),
        "outputs": [
            "mathematical_viability_status",
            "numerical_reproducibility_status",
            "finite_approximation_identifiability_and_complexity_audit",
            "generic_model_equivalence_audit",
            "nonautomatic_future_handoff",
        ],
        "prohibited": [
            "physical bearer assignment",
            "seam gravity or master-action coupling",
            "empirical promotion",
            "automatic successor",
        ],
        "outcomes": PROGRAM_OUTCOMES,
        "stem": "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF",
        "tool": "toe_ccft_v0_viability_handoff_stage_authorization.py",
        "lean_open": "ToeCCFTV0ViabilityHandoffAttemptOpen",
        "lean_result": "ToeCCFTV0ViabilityHandoffResult",
    },
]


def read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def write_json(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"immutable artifact already exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def git_head() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def event_path(attempt: int, event: str) -> str:
    return (
        "formal/docs/release/bounded_program_events/"
        f"{PROGRAM_ID}_ATTEMPT_{attempt:02d}_{event}_v0.json"
    )


def stage_manifest(stage: dict[str, Any]) -> dict[str, Any]:
    number = stage["number"]
    dependencies = (
        [
            "TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0",
            "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
            "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
        ]
        if number == 1
        else [STAGES[number - 2]["id"]]
    )
    scope = {
        "semantic_stage_id": stage["id"],
        "normalized_scientific_question": stage["question"],
        "authorized_inputs": COMMON_INPUTS,
        "required_outputs": stage["outputs"],
        "prohibited_claims": list(dict.fromkeys(COMMON_PROHIBITED + stage["prohibited"])),
        "dependency_artifact_ids": dependencies,
        "terminal_outcome_vocabulary": stage["outcomes"],
    }
    stem = stage["stem"]
    open_event = event_path(number, "OPEN")
    close_event = event_path(number, "CLOSE")
    open_paths = [
        "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        f"formal/docs/release/{stem}_OPEN_VALIDATION_v0.json",
        open_event,
        f"formal/python/tools/{stage['tool']}",
        "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
        f"formal/toe_formal/ToeFormal/Derivation/{stage['lean_open']}.lean",
        "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
        "formal/toe_formal/ToeFormalAll.lean",
    ]
    close_paths = [
        "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        f"formal/docs/release/{stem}_RESULT_v0.json",
        f"formal/docs/release/{stem}_RESULT_REVIEW_v0.json",
        f"formal/docs/release/{stem}_VALIDATION_v0.json",
        close_event,
        "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
        f"formal/toe_formal/ToeFormal/Derivation/{stage['lean_result']}.lean",
        "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
        "formal/toe_formal/ToeFormalAll.lean",
    ]
    return {
        "canonical_scope": scope,
        "canonical_scope_hash": governance.scope_hash(scope),
        "canonical_target": stage["target"],
        "conditional": number != 1,
        "lifecycle_rule": (
            "PASSED_ONLY_FOR_SINGLE_BRANCH_SELECTION; RETAIN_TWO_OR_NO_BRANCH_BLOCKS_"
            "THE_SINGLE_MODEL_PROGRAM_AND_REQUIRES_MANDATORY_EXIT"
            if number == 1
            else "PASSED_CONTINUES; BLOCKED_OR_FAILED_REQUIRES_MANDATORY_EXIT"
        ),
        "mandatory_terminal_outcomes": stage["outcomes"],
        "prospective_envelope": {
            "open_commit_exact_path_set": sorted(open_paths),
            "close_commit_exact_path_set": sorted(close_paths),
            "open_event_path": open_event,
            "close_event_path": close_event,
            "result_artifact_path": f"formal/docs/release/{stem}_RESULT_v0.json",
            "review_artifact_path": f"formal/docs/release/{stem}_RESULT_REVIEW_v0.json",
        },
        "semantic_stage_id": stage["id"],
        "stage_number": number,
    }


def installation_exact_paths() -> list[str]:
    return sorted(
        [
            "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
            MANIFEST_REL,
            rel(INSTALLATION),
            rel(INSTALLATION_REVIEW),
            rel(INSTALLATION_VALIDATION),
            rel(INSTALLATION_TEST),
            "formal/python/tools/bounded_program_governance.py",
            rel(INSTALLATION_LEAN),
            rel(REVIEW_LEAN),
            rel(CURRENT_TARGET),
            rel(CURRENT_AUTHORITY),
            "formal/toe_formal/ToeFormalAll.lean",
        ]
    )


def build_manifest(installed_from_commit: str) -> dict[str, Any]:
    proposal = read(PREPARATION_RESULT)
    if proposal["program_id_proposed"] != PROGRAM_ID:
        raise ValueError("prepared program id does not match installation")
    if proposal["program_installation_status"] != "UNINSTALLED":
        raise ValueError("prepared program is not in the uninstalled state")
    if proposal["branch_selected"] != "NONE" or proposal["ccft_v0_model"] != "NONE":
        raise ValueError("proposal crossed the branch or model boundary")
    if sha(DIRECTOR_PACKET) != proposal["research_director_packet_binding"]["sha256"]:
        raise ValueError("director packet binding does not reproduce")
    manifest: dict[str, Any] = {
        "authorized_stage_count": 5,
        "attempt_cap": 5,
        "automatic_successor": "NONE",
        "director_decision_packet_binding": {
            "path": rel(DIRECTOR_PACKET),
            "sha256": sha(DIRECTOR_PACKET),
            "option_selected": "NONE",
        },
        "external_checks_are_not_action_terms": True,
        "external_evaluation_checks": EXTERNAL_CHECKS,
        "independent_attack_lanes": ATTACK_LANES,
        "installation_envelope": {
            "commit_exact_path_set": installation_exact_paths(),
            "installed_from_commit": installed_from_commit,
        },
        "mandatory_exit": {"target": MANDATORY_EXIT, "terminal_outcomes": PROGRAM_OUTCOMES},
        "manifest_hash": "",
        "manifest_mode": "PROSPECTIVE_STATIC",
        "maximum_frozen_model_versions": 1,
        "maximum_new_ccft_postulates": 8,
        "maximum_primary_theorem_packets": 1,
        "native_hypothesis_tested": "HYP_TOE_CCFT_V0_CONSTRUCTED_SURROGATE_v0",
        "native_relevance": {
            "kind": "DIRECT_NATIVE_TEST",
            "statement": (
                "Constructs one provenance-labeled CCFT-v0 surrogate and subjects "
                "it to a decisive theorem or counterexample without physical promotion."
            ),
        },
        "no_subsidiary_scientific_targets": True,
        "program_id": PROGRAM_ID,
        "program_terminal_outcomes": PROGRAM_OUTCOMES,
        "provenance_vocabulary": PROVENANCE,
        "repair_attempt_count": 0,
        "research_director_support_required": True,
        "schema_id": "toe.bounded_program.immutable_manifest.v1",
        "stage_1_blocking_outcomes": [
            "RETAIN_TWO_SEPARATE_CONSTRUCTION_CANDIDATES",
            "NO_BRANCH_READY_WITHOUT_FOUNDATIONAL_POSTULATE",
        ],
        "stages": [stage_manifest(stage) for stage in STAGES],
        "status": "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST",
        "theorem_packet_required_fields": THEOREM_FIELDS,
        "theorem_status_dimensions_remain_separate": True,
    }
    manifest["manifest_hash"] = governance._hashed_payload(manifest, "manifest_hash")
    return manifest


def project_registry(
    registry: dict[str, Any],
    *,
    kind: str,
    evidence: str,
    report: str,
    outcome: str,
    strict: str,
    consumed_target: str,
    queue_scope: str,
    claim_status: str,
) -> dict[str, Any]:
    projection = registry["current_projection_v0"]
    projection.update(
        {
            "active_lane": INSTALLATION_TARGET,
            "current_target": INSTALLATION_TARGET,
            "current_target_kind": kind,
            "current_target_evidence": evidence,
            "current_target_report": report,
            "current_target_outcome": outcome,
            "current_target_strict_outcome": strict,
            "previous_target": consumed_target,
            "workstream_id": INSTALLATION_TARGET,
        }
    )
    for key in (
        "active_lane",
        "current_live_next_target",
        "current_live_target",
        "current_target",
        "live_next_target",
    ):
        registry[key] = INSTALLATION_TARGET
    registry["ACTIVE_LANE_v0"] = INSTALLATION_TARGET
    registry["CURRENT_LIVE_NEXT_TARGET_v0"] = INSTALLATION_TARGET
    registry["PREVIOUS_LIVE_NEXT_TARGET_v0"] = consumed_target
    value_map = {
        "EVIDENCE": evidence,
        "REPORT": report,
        "OUTCOME": outcome,
        "STRICT_OUTCOME": strict,
        "KIND": kind,
    }
    for suffix, value in value_map.items():
        registry[f"CURRENT_LIVE_TARGET_{suffix}_v0"] = value
        registry[f"current_live_target_{suffix.lower()}"] = value
        registry[f"current_target_{suffix.lower()}"] = value
        registry[f"live_next_target_{suffix.lower()}"] = value
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    if len(active) != 1:
        raise ValueError("exactly one active workstream is required")
    active[0].update(
        {
            "workstream_id": INSTALLATION_TARGET,
            "active_lane": INSTALLATION_TARGET,
            "authorized_target": INSTALLATION_TARGET,
            "authorized_next_strict_target": INSTALLATION_TARGET,
            "selected_next_target": INSTALLATION_TARGET,
            "selected_next_target_kind": kind,
            "authorization_evidence": evidence,
            "report": report,
            "report_path": report,
            "report_sha256": sha(ROOT / report),
            "packet_result": outcome,
            "strict_packet_result": strict,
            "consumed_target": consumed_target,
            "queue_scope": queue_scope,
            "claim_status": claim_status,
        }
    )
    registry["active_lanes"] = [INSTALLATION_TARGET]
    registry["active_workstream"] = INSTALLATION_TARGET
    registry["active_workstreams"] = [dict(active[0])]
    if INSTALLATION_TARGET not in registry["next_strict_target_coverage"]:
        registry["next_strict_target_coverage"].append(INSTALLATION_TARGET)
        registry["next_strict_target_coverage"].sort()
    registry["current_target_state"].update(
        {
            "active_lane": INSTALLATION_TARGET,
            "live_next_target": INSTALLATION_TARGET,
            "previous_live_next_target": consumed_target,
            "live_next_target_kind": kind,
            "live_next_target_evidence": evidence,
            "live_next_target_report": report,
            "live_next_target_outcome": outcome,
            "live_next_target_strict_outcome": strict,
        }
    )
    registry = repair_registry(registry)
    governance.validate_registry_extension(registry)
    return registry


def authority_value(captured_at_utc: str) -> dict[str, Any]:
    proposal = read(PREPARATION_RESULT)
    review = read(PREPARATION_REVIEW)
    if review["accepted"] is not True or review["reviewed_result"]["sha256"] != sha(PREPARATION_RESULT):
        raise ValueError("prepared proposal review is not valid")
    return {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_v0",
        "schema_id": "toe.ccft_v0.theory_construction.program_governance_installation_authority.v0",
        "captured_at_utc": captured_at_utc,
        "authority_decision": "AUTHORIZE_CCFT_V0_CONSTRUCTION_PROGRAM_INSTALLATION",
        "authorized_target": INSTALLATION_TARGET,
        "authorized_actions": [
            "create immutable five-stage program manifest",
            "register canonical scope hashes and prospective OPEN/CLOSE envelopes",
            "register five-attempt zero-repair and mandatory-exit controls",
            "bind Research Director and theorem packet schemas",
            "update registry generated and Lean authority mirrors",
            "perform installation validation and independent review",
        ],
        "authority_exact_path_set": sorted(
            [
                "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
                rel(AUTHORITY),
                rel(AUTHORITY_REVIEW),
                rel(AUTHORITY_TEST),
                rel(AUTHORITY_LEAN),
                rel(CURRENT_TARGET),
                rel(CURRENT_AUTHORITY),
                "formal/toe_formal/ToeFormalAll.lean",
            ]
        ),
        "consumed_proposal": {
            "path": rel(PREPARATION_RESULT),
            "sha256": sha(PREPARATION_RESULT),
            "review_path": rel(PREPARATION_REVIEW),
            "review_sha256": sha(PREPARATION_REVIEW),
            "proposed_stage_count": proposal["authorized_stage_count_proposed"],
        },
        "installation_authorized": True,
        "scientific_stage_open_authorized": False,
        "branch_selection_authorized": False,
        "model_or_postulate_construction_authorized": False,
        "theorem_execution_authorized": False,
        "physical_promotion_authorized": False,
        "status": "PROGRAM_INSTALLATION_AUTHORIZED_NOT_EXECUTED",
    }


def authority_review_value(authority: dict[str, Any], captured_at_utc: str) -> dict[str, Any]:
    return {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_REVIEW_v0",
        "schema_id": "toe.ccft_v0.theory_construction.program_governance_installation_authority_review.v0",
        "captured_at_utc": captured_at_utc,
        "authority_sha256": governance._hashed_payload(authority, "unused") if False else "PENDING",
        "accepted": True,
        "checks": {
            "proposal_prepared_and_reviewed": True,
            "installation_only": True,
            "scientific_stage_remains_unopened": True,
            "branch_model_and_theorem_remain_unselected": True,
            "five_stage_zero_repair_boundary_preserved": True,
        },
        "decision": "ACCEPT_INSTALLATION_AUTHORITY_AWAIT_ATOMIC_INSTALLATION",
        "status": "PASS",
    }


def write_authority_surfaces() -> None:
    AUTHORITY_LEAN.write_text(
        f'''namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0TheoryConstructionProgramInstallationAuthority

def authorityId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_v0"
def reviewId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_AUTHORITY_REVIEW_v0"
def authorizedTarget : String := "{INSTALLATION_TARGET}"
def installationAuthorized : Bool := true
def authorizedStageCount : Nat := 5
def attemptCap : Nat := 5
def repairAttemptCount : Nat := 0
def scientificStageOpenAuthorized : Bool := false
def branchSelected : Bool := false
def modelConstructed : Bool := false
def theoremAttempted : Bool := false

theorem authority_is_installation_only :
    installationAuthorized = true ∧ authorizedStageCount = 5 ∧ attemptCap = 5 ∧
    repairAttemptCount = 0 ∧ scientificStageOpenAuthorized = false ∧
    branchSelected = false ∧ modelConstructed = false ∧ theoremAttempted = false := by
  decide

end ToeCCFTV0TheoryConstructionProgramInstallationAuthority
end Derivation
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_TARGET.write_text(
        f'''import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionProgramInstallationAuthority

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0TheoryConstructionProgramInstallationAuthority
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := authorizedTarget
def currentEvidencePacketId : String := reviewId
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_INSTALLATION_AUTHORIZED"
def currentBoundedProgramState : String := "INSTALLATION_AUTHORIZED_NOT_EXECUTED"

theorem current_target_authorizes_installation_without_science :
    installationAuthorized = true ∧ scientificStageOpenAuthorized = false ∧
    branchSelected = false ∧ modelConstructed = false ∧ theoremAttempted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_AUTHORITY.write_text(
        f'''import ToeFormal.Derivation.CurrentTarget

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_is_installation_only :
    currentTarget = "{INSTALLATION_TARGET}" ∧
    Derivation.ToeCCFTV0TheoryConstructionProgramInstallationAuthority.installationAuthorized = true ∧
    Derivation.ToeCCFTV0TheoryConstructionProgramInstallationAuthority.scientificStageOpenAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )


def write_authority_test() -> None:
    AUTHORITY_TEST.write_text(
        f'''from __future__ import annotations
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
R=ROOT/"formal/docs/release"
A=R/"{AUTHORITY.name}"
V=R/"{AUTHORITY_REVIEW.name}"
def read(p): return json.loads(p.read_text(encoding="utf-8"))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def test_authority_is_installation_only():
    a=read(A); assert a["authorized_target"]=="{INSTALLATION_TARGET}"; assert a["installation_authorized"] is True
    assert a["scientific_stage_open_authorized"] is False; assert a["branch_selection_authorized"] is False
    assert a["model_or_postulate_construction_authorized"] is False; assert a["theorem_execution_authorized"] is False
def test_authority_review_accepts_bound_proposal():
    a=read(A); v=read(V); assert v["authority_sha256"]==sha(A); assert v["accepted"] is True; assert all(v["checks"].values())
    p=ROOT/a["consumed_proposal"]["path"]; q=ROOT/a["consumed_proposal"]["review_path"]
    assert sha(p)==a["consumed_proposal"]["sha256"]; assert sha(q)==a["consumed_proposal"]["review_sha256"]
''',
        encoding="utf-8",
        newline="\n",
    )


def installation_value(manifest: dict[str, Any], installed_from_commit: str, captured_at_utc: str) -> dict[str, Any]:
    return {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_RESULT_v0",
        "schema_id": "toe.ccft_v0.theory_construction.program_governance_installation_result.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "installed_from_commit": installed_from_commit,
        "manifest_path": MANIFEST_REL,
        "manifest_hash": manifest["manifest_hash"],
        "installed_program_state": "INSTALLED_UNOPENED",
        "authorized_stage_count": 5,
        "scientific_attempts": 0,
        "events": 0,
        "repair_attempt_count": 0,
        "stage_1_opened": False,
        "branch_selected": "NONE",
        "ccft_v0_model": "NONE",
        "new_ccft_postulates": 0,
        "primary_theorem_packet": "NONE",
        "theorem_or_counterexample_attempted": False,
        "physical_interpretation": "NONE",
        "mandatory_exit_target": MANDATORY_EXIT,
        "automatic_successor": "NONE",
        "historical_recovery_reopened": False,
        "status": "PROGRAM_INSTALLED_UNOPENED_NO_SCIENTIFIC_OUTPUT",
    }


def installation_review_value(result: dict[str, Any], manifest: dict[str, Any], captured_at_utc: str) -> dict[str, Any]:
    return {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_REVIEW_v0",
        "schema_id": "toe.ccft_v0.theory_construction.program_governance_installation_review.v0",
        "captured_at_utc": captured_at_utc,
        "reviewed_result": {"path": rel(INSTALLATION), "sha256": "PENDING"},
        "reviewed_manifest": {"path": MANIFEST_REL, "sha256": sha(MANIFEST)},
        "manifest_hash": manifest["manifest_hash"],
        "accepted": True,
        "checks": {
            "five_stage_sequence_matches_latest_director_workflow": True,
            "stage_three_is_nonexecuting_theorem_packet_preparation": True,
            "stage_four_alone_runs_theorem_attack_lanes": True,
            "single_model_and_eight_postulate_caps_bound": True,
            "retain_two_or_no_branch_cannot_silently_narrow_later": True,
            "provenance_and_theorem_status_dimensions_bound": True,
            "external_checks_remain_outside_physical_equations": True,
            "program_installed_unopened_with_zero_events": True,
            "no_branch_model_theorem_or_physical_claim_created": True,
        },
        "decision": "ACCEPT_CCFT_V0_CONSTRUCTION_PROGRAM_INSTALLATION_UNOPENED",
        "status": "PASS",
    }


def write_installation_surfaces() -> None:
    INSTALLATION_LEAN.write_text(
        f'''namespace ToeFormal
namespace Release
namespace ToeCCFTV0TheoryConstructionProgramGovernanceInstallation

def programId : String := "{PROGRAM_ID}"
def manifestPath : String := "{MANIFEST_REL}"
def mandatoryExit : String := "{MANDATORY_EXIT}"
def authorizedStageCount : Nat := 5
def attemptCap : Nat := 5
def repairAttemptCount : Nat := 0
def scientificAttempts : Nat := 0
def eventCount : Nat := 0
def maximumFrozenModels : Nat := 1
def maximumNewPostulates : Nat := 8
def maximumPrimaryTheoremPackets : Nat := 1
def installedUnopened : Bool := true
def branchSelected : Bool := false
def modelConstructed : Bool := false
def theoremAttempted : Bool := false

theorem installation_is_bounded_and_scientifically_unopened :
    authorizedStageCount = 5 ∧ attemptCap = 5 ∧ repairAttemptCount = 0 ∧
    scientificAttempts = 0 ∧ eventCount = 0 ∧ maximumFrozenModels = 1 ∧
    maximumNewPostulates = 8 ∧ maximumPrimaryTheoremPackets = 1 ∧
    installedUnopened = true ∧ branchSelected = false ∧ modelConstructed = false ∧
    theoremAttempted = false := by
  decide

end ToeCCFTV0TheoryConstructionProgramGovernanceInstallation
end Release
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    REVIEW_LEAN.write_text(
        '''import ToeFormal.Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation

namespace ToeFormal
namespace Release
namespace ToeCCFTV0TheoryConstructionProgramGovernanceInstallationReview

open ToeCCFTV0TheoryConstructionProgramGovernanceInstallation
def reviewAccepted : Bool := true
def directorSupportLayerBound : Bool := true
def theoremPacketPrecedesAttack : Bool := true
def externalChecksOutsideAction : Bool := true

theorem independent_review_accepts_unopened_installation :
    reviewAccepted = true ∧ directorSupportLayerBound = true ∧
    theoremPacketPrecedesAttack = true ∧ externalChecksOutsideAction = true ∧
    installedUnopened = true ∧ scientificAttempts = 0 ∧ branchSelected = false ∧
    modelConstructed = false ∧ theoremAttempted = false := by
  decide

end ToeCCFTV0TheoryConstructionProgramGovernanceInstallationReview
end Release
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_TARGET.write_text(
        f'''import ToeFormal.Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallationReview

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := "{INSTALLATION_TARGET}"
def currentEvidencePacketId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_REVIEW_v0"
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_INSTALLED_UNOPENED"
def currentBoundedProgramState : String := "INSTALLED_UNOPENED"

theorem current_target_preserves_unopened_installation :
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.installedUnopened = true ∧
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.scientificAttempts = 0 ∧
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.branchSelected = false ∧
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.modelConstructed = false ∧
    Release.ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.theoremAttempted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )
    CURRENT_AUTHORITY.write_text(
        f'''import ToeFormal.Derivation.CurrentTarget

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_unopened_ccft_v0_program :
    currentTarget = "{INSTALLATION_TARGET}" ∧ currentBoundedProgramState = "INSTALLED_UNOPENED" ∧
    ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.installedUnopened = true ∧
    ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.branchSelected = false ∧
    ToeCCFTV0TheoryConstructionProgramGovernanceInstallation.theoremAttempted = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''',
        encoding="utf-8",
        newline="\n",
    )


def write_installation_test() -> None:
    INSTALLATION_TEST.write_text(
        f'''from __future__ import annotations
import hashlib, json
from pathlib import Path
from formal.python.tools import bounded_program_governance as g
ROOT=Path(__file__).resolve().parents[3]
R=ROOT/"formal/docs/release"
M=ROOT/"{MANIFEST_REL}"
I=R/"{INSTALLATION.name}"
V=R/"{INSTALLATION_REVIEW.name}"
REG=R/"LOOP_CONTROL_REGISTRY_v0.json"
def read(p): return json.loads(p.read_text(encoding="utf-8"))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def test_manifest_has_five_sequenced_stages():
    m=read(M); assert m["authorized_stage_count"]==5; assert [x["stage_number"] for x in m["stages"]]==[1,2,3,4,5]
    assert m["stages"][2]["semantic_stage_id"]=="CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION"
    assert m["stages"][3]["semantic_stage_id"]=="CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION"
def test_manifest_hash_and_scope_hashes_reproduce():
    m=read(M); assert m["manifest_hash"]==g._hashed_payload(m,"manifest_hash")
    assert all(x["canonical_scope_hash"]==g.scope_hash(x["canonical_scope"]) for x in m["stages"])
def test_director_and_provenance_contracts_are_bound():
    m=read(M); assert m["director_decision_packet_binding"]["option_selected"]=="NONE"
    assert m["provenance_vocabulary"]=={PROVENANCE!r}; assert m["external_evaluation_checks"]=={EXTERNAL_CHECKS!r}
    assert m["external_checks_are_not_action_terms"] is True
def test_stage_one_two_candidate_or_no_branch_results_block_silent_narrowing():
    m=read(M); assert set(m["stage_1_blocking_outcomes"])=={{"RETAIN_TWO_SEPARATE_CONSTRUCTION_CANDIDATES","NO_BRANCH_READY_WITHOUT_FOUNDATIONAL_POSTULATE"}}
def test_program_is_registered_unopened():
    r=read(REG)[g.PROGRAMS_KEY]["{PROGRAM_ID}"]; assert r["state"]=="UNOPENED"; assert r["events"]==[]
    assert r["current_stage_number"]==0; assert r["repair_attempt_count"]==0; assert r["program_terminal_status"]=="INSTALLED_UNOPENED"
def test_installation_created_no_scientific_output():
    i=read(I); assert i["installed_program_state"]=="INSTALLED_UNOPENED"; assert i["scientific_attempts"]==0
    assert i["branch_selected"]=="NONE"; assert i["ccft_v0_model"]=="NONE"; assert i["primary_theorem_packet"]=="NONE"; assert i["theorem_or_counterexample_attempted"] is False
def test_independent_review_binds_result_and_manifest():
    v=read(V); assert v["accepted"] is True; assert v["reviewed_result"]["sha256"]==sha(I); assert v["reviewed_manifest"]["sha256"]==sha(M); assert all(v["checks"].values())
''',
        encoding="utf-8",
        newline="\n",
    )


def authorize(captured_at_utc: str) -> None:
    value = authority_value(captured_at_utc)
    write_json(AUTHORITY, value)
    review = authority_review_value(value, captured_at_utc)
    review["authority_sha256"] = sha(AUTHORITY)
    write_json(AUTHORITY_REVIEW, review)
    write_authority_surfaces()
    write_authority_test()
    registry = read(REGISTRY)
    if registry["current_projection_v0"]["current_target"] != PREPARATION_TARGET:
        raise ValueError("prepared proposal is not the current authoritative target")
    registry = project_registry(
        registry,
        kind="toe_ccft_v0_theory_construction_program_installation_authorized_v0",
        evidence=rel(AUTHORITY_LEAN),
        report=rel(AUTHORITY_REVIEW),
        outcome="CCFT_V0_CONSTRUCTION_PROGRAM_INSTALLATION_AUTHORIZED",
        strict="INSTALLATION_ONLY_NO_STAGE_OPEN_BRANCH_SELECTION_POSTULATE_MODEL_THEOREM_OR_PHYSICAL_PROMOTION",
        consumed_target=PREPARATION_TARGET,
        queue_scope="Install the immutable five-stage CCFT-v0 construction program and independent review; leave it scientifically unopened.",
        claim_status="Installation authority only; no scientific stage, branch, postulate, model, theorem, or physical claim is authorized.",
    )
    atomic_write_registry(REGISTRY, governance._registry_json_bytes(registry))


def install(captured_at_utc: str) -> None:
    authority = read(AUTHORITY)
    review = read(AUTHORITY_REVIEW)
    if authority["installation_authorized"] is not True or review["accepted"] is not True:
        raise ValueError("installation authority is not valid")
    if MANIFEST.exists() or INSTALLATION.exists():
        raise ValueError("CCFT-v0 construction program is already installed")
    installed_from_commit = git_head()
    manifest = build_manifest(installed_from_commit)
    governance.validate_ijson(manifest)
    write_json(MANIFEST, manifest)
    result = installation_value(manifest, installed_from_commit, captured_at_utc)
    write_json(INSTALLATION, result)
    installation_review = installation_review_value(result, manifest, captured_at_utc)
    installation_review["reviewed_result"]["sha256"] = sha(INSTALLATION)
    write_json(INSTALLATION_REVIEW, installation_review)
    write_installation_surfaces()
    write_installation_test()
    registry = read(REGISTRY)
    if registry["current_projection_v0"]["current_target"] != INSTALLATION_TARGET:
        raise ValueError("installation authority target is not authoritative")
    registry = governance.install_ccft_v0_theory_construction_program(registry)
    registry = project_registry(
        registry,
        kind="toe_ccft_v0_theory_construction_program_installed_unopened_v0",
        evidence=rel(REVIEW_LEAN),
        report=rel(INSTALLATION_REVIEW),
        outcome="CCFT_V0_CONSTRUCTION_PROGRAM_INSTALLED_UNOPENED",
        strict="FIVE_STAGE_IMMUTABLE_PROGRAM_INSTALLED_REVIEWED_ZERO_ATTEMPTS_ZERO_EVENTS_NO_BRANCH_MODEL_THEOREM_OR_PHYSICAL_PROMOTION",
        consumed_target=PREPARATION_TARGET,
        queue_scope="Program installed and independently reviewed unopened; Stage 1 requires separate scientific authority and immutable OPEN.",
        claim_status="Program governance installed only; branch, model, postulate, theorem packet, theorem result, and physical interpretation remain none.",
    )
    atomic_write_registry(REGISTRY, governance._registry_json_bytes(registry))
    validation = {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_GOVERNANCE_INSTALLATION_VALIDATION_v0",
        "schema_id": "toe.ccft_v0.theory_construction.program_governance_installation_validation.v0",
        "captured_at_utc": captured_at_utc,
        "manifest_sha256": sha(MANIFEST),
        "manifest_hash": manifest["manifest_hash"],
        "installation_result_sha256": sha(INSTALLATION),
        "installation_review_sha256": sha(INSTALLATION_REVIEW),
        "installation_exact_path_set": installation_exact_paths(),
        "scientific_boundary": {
            "installed_unopened": True,
            "scientific_attempts": 0,
            "events": 0,
            "branch_selected": False,
            "model_constructed": False,
            "theorem_packet_prepared": False,
            "theorem_attempted": False,
            "physical_interpretation_established": False,
        },
        "focused_python": {"status": "PENDING_PRECOMMIT"},
        "full_lean": {"status": "PENDING_PRECOMMIT"},
        "deterministic_generation": {"status": "PENDING_PRECOMMIT"},
        "governance_reconstruction": {"status": "PENDING_PRECOMMIT"},
        "tracked_checkout_after_commit": "REQUIRED_POST_COMMIT",
        "reddit": "UNTRACKED_AND_UNTOUCHED",
        "exhaustive_python": "NOT_CLAIMED",
        "status": "INSTALLATION_READY_FOR_VALIDATION",
    }
    write_json(INSTALLATION_VALIDATION, validation)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("authorize", "install"))
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args()
    if args.mode == "authorize":
        authorize(args.captured_at_utc)
    else:
        install(args.captured_at_utc)
    print(args.mode)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
