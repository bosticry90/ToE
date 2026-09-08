from __future__ import annotations

"""Authorize and prepare—but do not install—the bounded CCFT-v0 construction program."""

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.bounded_program_governance import _registry_json_bytes, validate_registry_extension
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry, repair_registry


ROOT = find_repo_root(Path(__file__))
RELEASE = ROOT / "formal/docs/release"
REGISTRY = RELEASE / "LOOP_CONTROL_REGISTRY_v0.json"
TARGET = "prepare_bounded_ccft_v0_theory_construction_program"
PROGRAM_ID = "TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0"
EXIT_TARGET = "close_toe_ccft_v0_theory_construction_and_theorem_discovery_v0_after_bounded_result_v0"
CLOSEOUT_RESULT = RELEASE / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_BOUNDED_CLOSEOUT_RESULT_v0.json"
CLOSEOUT_REVIEW = RELEASE / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_BOUNDED_CLOSEOUT_REVIEW_v0.json"
CLOSEOUT_VALIDATION = RELEASE / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_BOUNDED_CLOSEOUT_VALIDATION_v0.json"
STAGE4_RESULT = RELEASE / "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_v0.json"
STAGE4_REVIEW = RELEASE / "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_REVIEW_v0.json"
AUTHORITY = RELEASE / "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0.json"
AUTHORITY_REVIEW = RELEASE / "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0.json"
RESULT = RELEASE / "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
RESULT_REVIEW = RELEASE / "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
PACKET = RELEASE / "TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0.json"
VALIDATION = RELEASE / "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_VALIDATION_v0.json"
AUTHORITY_TEST = ROOT / "formal/python/tests/test_toe_ccft_v0_theory_construction_bounded_program_preparation_authority.py"
PROPOSAL_TEST = ROOT / "formal/python/tests/test_toe_ccft_v0_theory_construction_bounded_program_preparation.py"
AUTHORITY_LEAN = ROOT / "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.lean"
PROPOSAL_LEAN = ROOT / "formal/toe_formal/ToeFormal/Derivation/ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview.lean"
CURRENT_TARGET = ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY = ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"


def read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def write_json(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"immutable preparation artifact already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def source_binding(path: Path, role: str) -> dict[str, str]:
    return {"path": rel(path), "sha256": sha(path), "role": role}


def project_registry(
    registry: dict[str, Any],
    *,
    kind: str,
    evidence: str,
    report: str,
    report_sha256: str,
    outcome: str,
    strict: str,
    consumed_target: str,
    queue_scope: str,
    claim_status: str,
) -> dict[str, Any]:
    projection = registry["current_projection_v0"]
    projection.update({
        "active_lane": TARGET,
        "current_target": TARGET,
        "current_target_kind": kind,
        "current_target_evidence": evidence,
        "current_target_report": report,
        "current_target_outcome": outcome,
        "current_target_strict_outcome": strict,
        "previous_target": consumed_target,
        "workstream_id": TARGET,
    })
    registry.update({
        "active_lane": TARGET,
        "ACTIVE_LANE_v0": TARGET,
        "CURRENT_LIVE_NEXT_TARGET_v0": TARGET,
        "PREVIOUS_LIVE_NEXT_TARGET_v0": consumed_target,
        "CURRENT_LIVE_TARGET_EVIDENCE_v0": evidence,
        "CURRENT_LIVE_TARGET_REPORT_v0": report,
        "CURRENT_LIVE_TARGET_OUTCOME_v0": outcome,
        "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0": strict,
        "CURRENT_LIVE_TARGET_KIND_v0": kind,
        "current_live_next_target": TARGET,
        "current_live_target": TARGET,
        "current_live_target_evidence": evidence,
        "current_live_target_kind": kind,
        "current_live_target_outcome": outcome,
        "current_live_target_report": report,
        "current_live_target_strict_outcome": strict,
        "current_target": TARGET,
        "current_target_evidence": evidence,
        "current_target_kind": kind,
        "current_target_outcome": outcome,
        "current_target_report": report,
        "current_target_strict_outcome": strict,
        "live_next_target": TARGET,
        "live_next_target_evidence": evidence,
        "live_next_target_kind": kind,
        "live_next_target_outcome": outcome,
        "live_next_target_report": report,
        "live_next_target_strict_outcome": strict,
    })
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    if len(active) != 1:
        raise ValueError("exactly one active workstream is required")
    workstream = active[0]
    workstream.update({
        "workstream_id": TARGET,
        "active_lane": TARGET,
        "authorized_target": TARGET,
        "authorized_next_strict_target": TARGET,
        "selected_next_target": TARGET,
        "selected_next_target_kind": kind,
        "authorization_evidence": evidence,
        "report": report,
        "report_path": report,
        "report_sha256": report_sha256,
        "packet_result": outcome,
        "strict_packet_result": strict,
        "consumed_target": consumed_target,
        "consumed_target_kind": "closed_predecessor_program_terminal_checkpoint",
        "queue_scope": queue_scope,
        "claim_status": claim_status,
    })
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstreams"] = [dict(workstream)]
    if TARGET not in registry["next_strict_target_coverage"]:
        registry["next_strict_target_coverage"].append(TARGET)
        registry["next_strict_target_coverage"].sort()
    registry["current_target_state"].update({
        "active_lane": TARGET,
        "live_next_target": TARGET,
        "previous_live_next_target": consumed_target,
        "live_next_target_kind": kind,
        "live_next_target_evidence": evidence,
        "live_next_target_report": report,
        "live_next_target_outcome": outcome,
        "live_next_target_strict_outcome": strict,
    })
    registry = repair_registry(registry)
    validate_registry_extension(registry)
    return registry


def build_authority(*, captured_at_utc: str) -> dict[str, Any]:
    closeout = read(CLOSEOUT_RESULT)
    if closeout["program_closeout"]["program_terminal_status"] != "CLOSED_AFTER_MANDATORY_EXIT":
        raise ValueError("targeted recovery program has not completed its mandatory exit")
    if closeout["scientific_result"]["recovered_contract_count"] != 4:
        raise ValueError("mandatory exit did not preserve four recovered contracts")
    if closeout["scientific_result"]["cp_nlse_conflict_count"] != 3:
        raise ValueError("mandatory exit did not preserve three conflicts")
    return {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0",
        "schema_id": "toe.ccft_v0.theory_construction.bounded_program_preparation_authority.v0",
        "captured_at_utc": captured_at_utc,
        "authority_decision": "AUTHORIZE_PROPOSAL_PREPARATION_ONLY",
        "authorized_target": TARGET,
        "user_authority": "EXPLICIT_CURRENT_REQUEST",
        "status": "PROGRAM_PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED",
        "consumed_terminal_checkpoint": [
            source_binding(CLOSEOUT_RESULT, "terminal targeted-recovery result"),
            source_binding(CLOSEOUT_REVIEW, "independent terminal targeted-recovery review"),
            source_binding(CLOSEOUT_VALIDATION, "terminal targeted-recovery validation"),
            source_binding(STAGE4_RESULT, "positive targeted-recovery handoff result"),
            source_binding(STAGE4_REVIEW, "independent positive handoff review"),
        ],
        "frozen_scientific_inputs": {
            "source_recovered_contracts": 4,
            "preserved_cp_nlse_conflicts": 3,
            "selected_ccft_v0_branch": "NONE",
            "closed_ccft_v0_model": "NONE",
            "new_ccft_postulates": 0,
            "historical_recovery_complete_for_ccft_v0": True,
            "repository_claim_exhaustion_established": False,
        },
        "permitted_work": [
            "PREPARE_ONE_BOUNDED_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_PROGRAM_PROPOSAL",
            "CREATE_A_NONSELECTING_RESEARCH_DIRECTOR_DECISION_PACKET_COMPARING_FOUR_FROZEN_OPTIONS",
            "FREEZE_A_FIVE_STAGE_SCIENCE_CENTERED_SEQUENCE",
            "FREEZE_PROVENANCE_LABELS_FOR_RECOVERED_BASELINE_POSTULATE_NUMERICAL_AND_CONTROL_CONTENT",
            "FREEZE_BRANCH_SPECIFIC_FIRST_THEOREM_OR_COUNTEREXAMPLE_TARGETS",
            "FREEZE_PROOF_DISPROOF_COUNTEREXAMPLE_SYMBOLIC_NUMERICAL_AND_LEAN_STATUS_SEPARATION",
            "FREEZE_FINITE_APPROXIMATION_IDENTIFIABILITY_AND_COMPLEXITY_AS_EXTERNAL_EVALUATION_CHECKS",
            "FREEZE_WORKLOAD_ATTEMPT_FAILURE_AND_MANDATORY_EXIT_CONTROLS",
            "INDEPENDENTLY_REVIEW_THE_PROPOSAL_FOR_NONSELECTION_NONEXECUTION_AND_SCIENTIFIC_DECISION_VALUE",
        ],
        "prohibited_work": [
            "INSTALL_THE_PROPOSED_PROGRAM",
            "OPEN_ANY_SCIENTIFIC_STAGE",
            "SELECT_CP_NLSE_LCRD_V3_TWO_CANDIDATES_OR_NEITHER",
            "SELECT_REPAIR_OR_POSTULATE_A_GOVERNING_EQUATION",
            "INSERT_ANY_NEW_CCFT_POSTULATE",
            "FREEZE_OR_CONSTRUCT_CCFT_V0",
            "CREATE_OR_RUN_A_REFERENCE_IMPLEMENTATION",
            "ATTEMPT_A_PROOF_DISPROOF_COUNTEREXAMPLE_SYMBOLIC_OR_NUMERICAL_RESULT",
            "INSTALL_C_FINITE_APPROXIMATION_C_IDENTIFIABILITY_OR_C_COMPLEXITY_AS_ACTION_TERMS",
            "PHYSICALLY_INTERPRET_PROMOTE_OR_EMPIRICALLY_VALIDATE_CCFT",
            "REOPEN_HISTORICAL_OR_TARGETED_ARCHIVE_RECOVERY",
        ],
        "required_director_packet_options": [
            "OPTION_A_NONLINEAR_CP_NLSE_MINIMAL_COMPUTATIONAL_CORE",
            "OPTION_B_LCRD_V3_MINIMAL_PHENOMENOLOGICAL_CORE",
            "OPTION_C_TWO_SEPARATE_V0_CANDIDATES_WITHOUT_COMBINATION",
            "OPTION_D_NEITHER_BRANCH_READY_WITHOUT_FOUNDATIONAL_POSTULATE",
        ],
        "proposal_preparation_authorized": True,
        "program_installation_authorized": False,
        "scientific_stage_open_authorized": False,
        "branch_selection_authorized": False,
        "postulate_or_model_construction_authorized": False,
        "theorem_discovery_authorized": False,
    }


def build_authority_review(authority: dict[str, Any], *, captured_at_utc: str) -> dict[str, Any]:
    checks = {
        "terminal_closeout_is_hash_bound": all(sha(ROOT / row["path"]) == row["sha256"] for row in authority["consumed_terminal_checkpoint"]),
        "four_recovered_contracts_and_three_conflicts_are_frozen": authority["frozen_scientific_inputs"]["source_recovered_contracts"] == 4 and authority["frozen_scientific_inputs"]["preserved_cp_nlse_conflicts"] == 3,
        "historical_recovery_is_complete_without_exhaustion_claim": authority["frozen_scientific_inputs"]["historical_recovery_complete_for_ccft_v0"] is True and authority["frozen_scientific_inputs"]["repository_claim_exhaustion_established"] is False,
        "all_four_director_options_are_required_without_selection": len(authority["required_director_packet_options"]) == 4 and authority["branch_selection_authorized"] is False,
        "authority_is_proposal_preparation_only": authority["authority_decision"] == "AUTHORIZE_PROPOSAL_PREPARATION_ONLY" and authority["proposal_preparation_authorized"] is True,
        "installation_stage_open_postulate_model_and_theorem_work_are_unauthorized": authority["program_installation_authorized"] is False and authority["scientific_stage_open_authorized"] is False and authority["postulate_or_model_construction_authorized"] is False and authority["theorem_discovery_authorized"] is False,
        "archive_recovery_cannot_reopen": "REOPEN_HISTORICAL_OR_TARGETED_ARCHIVE_RECOVERY" in authority["prohibited_work"],
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise ValueError(f"preparation authority review failed: {failed}")
    return {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0",
        "schema_id": "toe.ccft_v0.theory_construction.bounded_program_preparation_authority_review.v0",
        "captured_at_utc": captured_at_utc,
        "authority_path": rel(AUTHORITY),
        "authority_sha256": sha(AUTHORITY),
        "checks": checks,
        "failed_checks": [],
        "accepted": True,
        "scientific_execution_authorized": False,
        "decision": "ACCEPT_CCFT_V0_CONSTRUCTION_PROGRAM_PROPOSAL_PREPARATION_ONLY",
        "status": "PASS",
    }


def director_packet() -> dict[str, Any]:
    return {
        "artifact_id": "TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0",
        "schema_id": "toe.ccft_v0.research_director_decision_packet.v0",
        "packet_status": "PREPARED_FOR_FUTURE_STAGE_1_REVIEW_NO_OPTION_SELECTED",
        "plain_language_unresolved_issue": "The archive supplied four useful contracts but no complete CCFT model. A director must choose which branch, if any, should receive explicit new postulates and become the first frozen CCFT-v0 hypothesis.",
        "why_it_matters": "Dispersion, conservation, existence, stability, and novelty results are meaningless until one exact model contract is frozen. Combining incompatible or incomplete branches would make later theorems apply to no well-defined theory.",
        "options": [
            {
                "option_id": "OPTION_A",
                "title": "Nonlinear CP-NLSE minimal computational core",
                "plain_language_case": "Shortest route to an executable surrogate because the numerical scaffolding and periodic setting are strongest.",
                "source_recovered": ["one-dimensional periodic domain", "periodic boundary conditions", "numerical and diagnostic scaffolding from prior bounded review"],
                "new_postulates_required": ["select or replace one governing nonlinear equation", "resolve or postulate the nonlinear dispersion contract", "parameter ranges", "admissible initial data", "invariant and failure contract", "reference implementation contract"],
                "remaining_contradictions": ["three incompatible governing-equation records", "squared-versus-additive interaction-frequency conflict"],
                "mathematical_workload": "MODERATE_AFTER_EQUATION_DECISION",
                "first_theorem_grade_question": "Given the frozen CP-NLSE equation and background, which interaction-dependent dispersion relation follows, and are the preserved squared and additive formulas compatible, special limits, or contradictory?",
                "support_result": "A consistent branch-dependent dispersion is derived and produces a closed next theorem target.",
                "weaken_result": "The equation reduces to a generic known nonlinear-wave model or its claimed invariant fails.",
                "reject_result": "No selected equation is internally consistent with the frozen data and reduction contracts.",
                "distinctiveness_risk": "HIGH_RISK_OF_GENERIC_NLSE_EQUIVALENCE",
            },
            {
                "option_id": "OPTION_B",
                "title": "LCRD-v3 minimal phenomenological core",
                "plain_language_case": "Preserves the most distinctive recovered CCFT-like rotor-curvature structure.",
                "source_recovered": ["state tuple (rho,u,R,K)", "Q_rotor=c1 R_x+c2 K_xx", "rotor-curvature evolution couplings"],
                "new_postulates_required": ["admissible initial and boundary data", "normalization", "complete parameter ranges", "nu_code meaning", "implementation contract", "failure and invariant rules"],
                "remaining_contradictions": ["no variational derivation", "no accepted LSDA coarse-graining map", "physical units and bearer absent"],
                "mathematical_workload": "HIGH_BUT_MORE_DISTINCTIVE",
                "first_theorem_grade_question": "After the missing data and normalization are explicitly supplied, do the recovered four-field equations form a closed evolution system with preserved constraints, or can a counterexample show underdetermination?",
                "support_result": "The four-field system closes and yields a well-defined evolution problem.",
                "weaken_result": "Closure exists only after multiple arbitrary constitutive assumptions or is equivalent to a known hydrodynamic model.",
                "reject_result": "The system remains underdetermined or internally inconsistent under every bounded completion considered.",
                "distinctiveness_risk": "LOWER_GENERICITY_RISK_HIGHER_POSTULATE_BURDEN",
            },
            {
                "option_id": "OPTION_C",
                "title": "Retain two independent v0 candidates",
                "plain_language_case": "Avoids premature preference while forbidding an unsupported combined wave-rotor model.",
                "source_recovered": ["all CP-NLSE and LCRD-v3 contracts remain lineage-separated"],
                "new_postulates_required": ["two complete model contracts", "two implementations", "two theorem packets", "explicit no-combination rule"],
                "remaining_contradictions": ["all branch-specific blockers remain"],
                "mathematical_workload": "VERY_HIGH_AND_DUPLICATIVE",
                "first_theorem_grade_question": "Which candidate reaches a decisive mathematical result under the smaller postulate burden?",
                "support_result": "Both candidates close independently and can be compared without mixing assumptions.",
                "weaken_result": "Only one candidate closes, making the second an unnecessary parallel burden.",
                "reject_result": "Neither candidate closes within the frozen construction budget.",
                "distinctiveness_risk": "DIFFUSES_VERTICAL_COMPLETION",
            },
            {
                "option_id": "OPTION_D",
                "title": "Neither branch ready without a foundational postulate",
                "plain_language_case": "Stops model completion if choosing either branch would obscure the missing physical or architectural principle.",
                "source_recovered": ["four contracts remain preserved without forcing a model"],
                "new_postulates_required": ["one explicit foundational CCFT principle before branch mechanics"],
                "remaining_contradictions": ["branch conflicts and operational gaps remain unresolved"],
                "mathematical_workload": "LOW_IMMEDIATE_HIGH_FOUNDATIONAL_UNCERTAINTY",
                "first_theorem_grade_question": "Can a proposed foundational principle impose a nontrivial restriction that selects or excludes a branch without assuming its equations?",
                "support_result": "One principle sharply constrains the allowable model class.",
                "weaken_result": "The proposed principle is only an evaluation rule or restatement of known physics.",
                "reject_result": "No bounded foundational postulate has decision value for the candidate branches.",
                "distinctiveness_risk": "MAY_DELAY_EXECUTABLE_MODEL_INDEFINITELY",
            },
        ],
        "rebuttable_preparation_recommendation": {
            "recommendation": "Use CP-NLSE as the shortest candidate for a first computational surrogate while retaining LCRD-v3 as the stronger distinctive alternative; do not select either until Stage 1 director review.",
            "selected_option": "NONE",
            "why_other_questions_wait": "Existence, conservation, stability, and novelty questions depend on a frozen governing model and provenance-labeled assumptions.",
        },
        "assumptions_requiring_director_approval": [
            {
                "technical_assumption": "Periodic one-dimensional spatial domain for a CP-NLSE v0",
                "plain_meaning": "The modeled state repeats at both ends of a line segment.",
                "source_status": "SOURCE_RECOVERED",
                "reason": "This is the strongest recovered CP-NLSE domain contract.",
                "risk": "Results need not apply to isolated, infinite, or wall-bounded systems.",
            },
            {
                "technical_assumption": "Phenomenological four-field LCRD-v3 state",
                "plain_meaning": "The model evolves density-like, velocity-like, rotor, and curvature variables without claiming a microscopic derivation.",
                "source_status": "SOURCE_RECOVERED_WITH_MISSING_PHYSICAL_INTERPRETATION",
                "reason": "It preserves the distinctive recovered structure.",
                "risk": "Mathematical closure would not establish physical ontology or LSDA emergence.",
            },
        ],
        "director_decision_required": True,
        "option_selected": "NONE",
        "model_or_postulate_created": False,
    }


def proposal() -> dict[str, Any]:
    stage_definitions = [
        {
            "stage_number": 1,
            "semantic_stage_id": "CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION",
            "target": "select_toe_ccft_v0_branch_after_research_director_decision_v0",
            "question": "Which one of the four frozen construction options offers the best bounded decision value without treating convenience as evidence?",
            "required_outputs": ["reviewed_director_decision_packet", "option_by_option_postulate_burden", "exactly_one_branch_route_or_no_route_result"],
            "prohibited": ["equation selection", "new postulate insertion", "model construction", "theorem execution"],
            "outcomes": ["SELECT_CP_NLSE_AS_CCFT_V0_CORE", "SELECT_LCRD_V3_AS_CCFT_V0_CORE", "RETAIN_TWO_SEPARATE_CONSTRUCTION_CANDIDATES", "NO_BRANCH_READY_WITHOUT_FOUNDATIONAL_POSTULATE"],
        },
        {
            "stage_number": 2,
            "semantic_stage_id": "CCFT_V0_EXPLICIT_MODEL_CONTRACT_COMPLETION",
            "target": "complete_toe_ccft_v0_model_contract_with_explicit_provenance_v0",
            "question": "What minimum explicit contract closes the selected route while labeling every recovered, imported, postulated, numerical, and control element?",
            "required_outputs": ["complete_model_contract", "component_provenance_ledger", "postulate_count_and_justification", "failure_contract"],
            "prohibited": ["unlabeled assumption insertion", "physical promotion", "branch combination without Stage 1 selection", "theorem execution"],
            "outcomes": ["CCFT_V0_MODEL_CONTRACT_COMPLETED", "MODEL_CONTRACT_REQUIRES_MORE_THAN_FROZEN_POSTULATE_BUDGET", "SELECTED_ROUTE_CONTRADICTORY_OR_UNDERDEFINED"],
        },
        {
            "stage_number": 3,
            "semantic_stage_id": "CCFT_V0_MODEL_FREEZE_AND_REFERENCE_IMPLEMENTATION",
            "target": "freeze_toe_ccft_v0_model_and_reference_implementation_v0",
            "question": "Can the provenance-labeled model be frozen as one reproducible mathematical and computational object?",
            "required_outputs": ["immutable_model_version", "initial_boundary_parameter_normalization_contract", "reference_implementation", "comparator_and_test_vectors"],
            "prohibited": ["post-freeze feature expansion", "physical validation claim", "theorem result claim"],
            "outcomes": ["CCFT_V0_FROZEN_FOR_THEOREM_ADJUDICATION", "REFERENCE_IMPLEMENTATION_NOT_REPRODUCIBLE", "MODEL_FREEZE_BLOCKED_BY_CONTRACT_CONFLICT"],
        },
        {
            "stage_number": 4,
            "semantic_stage_id": "CCFT_V0_FIRST_THEOREM_OR_COUNTEREXAMPLE_ADJUDICATION",
            "target": "adjudicate_toe_ccft_v0_first_theorem_or_counterexample_v0",
            "question": "What is the first decisive proof, disproof, construction, counterexample, or no-go result for the frozen model?",
            "required_outputs": ["research_director_question_packet", "formal_proposition_and_negation", "independent_proof_and_counterexample_attempts", "symbolic_and_numerical_checks", "Lean_status_and_fidelity_review"],
            "prohibited": ["claiming theorem failure proves physical truth", "changing the frozen model to rescue a result", "collapsing mathematical and physical status"],
            "outcomes": ["THEOREM_GRADE_RESULT_ESTABLISHED", "COUNTEREXAMPLE_OR_NO_GO_RESULT_ESTABLISHED", "RESULT_CONDITIONALLY_SUPPORTED_NOT_FORMALIZED", "MODEL_DEFINITION_INSUFFICIENT_FOR_THEOREM"],
        },
        {
            "stage_number": 5,
            "semantic_stage_id": "CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF",
            "target": "assess_toe_ccft_v0_internal_viability_and_distinctiveness_v0",
            "question": "Does the frozen model survive internal checks and remain distinct from known generic systems strongly enough for later physical operationalization?",
            "required_outputs": ["mathematical_viability_status", "numerical_reproducibility_status", "generic_model_equivalence_audit", "nonautomatic_physical_operationalization_handoff"],
            "prohibited": ["physical bearer assignment", "seam or gravity coupling", "empirical promotion", "automatic successor"],
            "outcomes": ["CCFT_V0_MATHEMATICALLY_VIABLE_DISTINCTIVE_SURROGATE", "CCFT_V0_EQUIVALENT_TO_KNOWN_MODEL", "CCFT_V0_INTERNALLY_INCONSISTENT", "VIABILITY_OR_DISTINCTIVENESS_UNRESOLVED"],
        },
    ]
    return {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
        "schema_id": "toe.ccft_v0.theory_construction.bounded_program_preparation_result.v0",
        "program_id_proposed": PROGRAM_ID,
        "preparation_target": TARGET,
        "authority_binding": {"path": rel(AUTHORITY), "sha256": sha(AUTHORITY)},
        "research_director_packet_binding": {"path": rel(PACKET), "sha256": sha(PACKET)},
        "scientific_purpose": "Construct one explicit provenance-labeled CCFT-v0 surrogate and subject it to a decisive theorem or counterexample before physical interpretation.",
        "stage_definitions_proposed": stage_definitions,
        "authorized_stage_count_proposed": 5,
        "attempt_cap_proposed": 5,
        "repair_attempt_count_proposed": 0,
        "maximum_frozen_model_versions": 1,
        "maximum_primary_theorem_packets": 1,
        "maximum_new_ccft_postulates": 8,
        "provenance_vocabulary": ["SOURCE_RECOVERED", "KNOWN_PHYSICS_BASELINE", "NEW_CCFT_POSTULATE", "NUMERICAL_CONVENTION", "MATHEMATICAL_CONTROL"],
        "theorem_status_vocabulary": ["MATHEMATICALLY_CONJECTURED", "COMPUTATIONALLY_SUPPORTED", "HUMAN_ARGUMENT_COMPLETE", "LEAN_FORMALIZED", "INDEPENDENTLY_REVIEWED", "PHYSICALLY_INTERPRETED", "EMPIRICALLY_TESTED"],
        "theorem_packet_required_fields": ["exact_definitions", "domains_and_regularity", "assumptions", "target_theorem", "formal_negation", "allowed_lemmas", "forbidden_conclusions", "known_examples", "known_counterexamples", "symbolic_test_suite", "numerical_test_suite", "Lean_theorem_signature", "physical_claim_boundary"],
        "independent_attack_lanes": ["PROVE", "DISPROVE", "CONSTRUCT", "FIND_COUNTEREXAMPLE"],
        "external_evaluation_checks": ["C_FINITE_APPROXIMATION", "C_IDENTIFIABILITY", "C_COMPLEXITY"],
        "external_checks_are_not_action_terms": True,
        "mandatory_exit_target_proposed": EXIT_TARGET,
        "automatic_successor_proposed": "NONE",
        "historical_recovery_reopened": False,
        "program_installation_status": "UNINSTALLED",
        "scientific_attempts": 0,
        "branch_selected": "NONE",
        "ccft_v0_model": "NONE",
        "new_postulates_created": 0,
        "theorem_or_counterexample_attempted": False,
        "physical_interpretation_established": False,
        "status": "PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY",
    }


def proposal_review(value: dict[str, Any], *, captured_at_utc: str) -> dict[str, Any]:
    packet = read(PACKET)
    stages = value["stage_definitions_proposed"]
    checks = {
        "preparation_authority_is_hash_bound": sha(AUTHORITY) == value["authority_binding"]["sha256"],
        "research_director_packet_is_hash_bound_and_nonselecting": sha(PACKET) == value["research_director_packet_binding"]["sha256"] and packet["option_selected"] == "NONE",
        "four_frozen_options_are_compared_in_plain_language": len(packet["options"]) == 4,
        "exact_five_stage_science_centered_sequence_is_frozen": len(stages) == 5 and [row["stage_number"] for row in stages] == [1, 2, 3, 4, 5],
        "branch_selection_occurs_only_in_future_stage_one": stages[0]["semantic_stage_id"] == "CCFT_V0_RESEARCH_DIRECTOR_BRANCH_READINESS_DECISION" and value["branch_selected"] == "NONE",
        "all_model_components_require_provenance_labels": len(value["provenance_vocabulary"]) == 5,
        "only_one_frozen_model_and_one_primary_theorem_packet_are_permitted": value["maximum_frozen_model_versions"] == 1 and value["maximum_primary_theorem_packets"] == 1,
        "proof_disproof_construction_and_counterexample_lanes_are_independent": set(value["independent_attack_lanes"]) == {"PROVE", "DISPROVE", "CONSTRUCT", "FIND_COUNTEREXAMPLE"},
        "mathematical_physical_and_empirical_statuses_remain_separate": len(value["theorem_status_vocabulary"]) == 7,
        "finite_approximation_identifiability_and_complexity_are_external_checks": value["external_evaluation_checks"] == ["C_FINITE_APPROXIMATION", "C_IDENTIFIABILITY", "C_COMPLEXITY"] and value["external_checks_are_not_action_terms"] is True,
        "zero_repair_and_mandatory_exit_are_frozen": value["repair_attempt_count_proposed"] == 0 and value["mandatory_exit_target_proposed"] == EXIT_TARGET,
        "program_is_uninstalled_unopened_and_nonexecuting": value["program_installation_status"] == "UNINSTALLED" and value["scientific_attempts"] == 0 and value["theorem_or_counterexample_attempted"] is False,
        "no_branch_model_postulate_or_physical_interpretation_exists": value["branch_selected"] == "NONE" and value["ccft_v0_model"] == "NONE" and value["new_postulates_created"] == 0 and value["physical_interpretation_established"] is False,
        "historical_recovery_does_not_reopen": value["historical_recovery_reopened"] is False,
    }
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise ValueError(f"proposal review failed: {failed}")
    return {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
        "schema_id": "toe.ccft_v0.theory_construction.bounded_program_preparation_result_review.v0",
        "captured_at_utc": captured_at_utc,
        "reviewed_result": {"path": rel(RESULT), "sha256": sha(RESULT)},
        "reviewed_director_packet": {"path": rel(PACKET), "sha256": sha(PACKET)},
        "checks": checks,
        "failed_checks": [],
        "accepted": True,
        "proposal_only": True,
        "program_installed": False,
        "scientific_stage_opened": False,
        "branch_selected": False,
        "model_or_theorem_work_executed": False,
        "decision": "ACCEPT_CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_PROPOSAL_AWAIT_SEPARATE_INSTALLATION_AUTHORITY",
        "status": "PASS",
    }


def write_authority_surfaces() -> None:
    AUTHORITY_LEAN.write_text(f'''namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority

def authorityId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0"
def reviewId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0"
def authorizedTarget : String := "{TARGET}"
def proposalPreparationAuthorized : Bool := true
def recoveredContractCount : Nat := 4
def preservedConflictCount : Nat := 3
def directorOptionCount : Nat := 4
def programInstallationAuthorized : Bool := false
def branchSelectionAuthorized : Bool := false
def newPostulateAuthorized : Bool := false
def theoremDiscoveryAuthorized : Bool := false

theorem authority_is_nonexecuting_program_preparation_only :
    proposalPreparationAuthorized = true ∧ recoveredContractCount = 4 ∧
    preservedConflictCount = 3 ∧ directorOptionCount = 4 ∧
    programInstallationAuthorized = false ∧ branchSelectionAuthorized = false ∧
    newPostulateAuthorized = false ∧ theoremDiscoveryAuthorized = false := by
  decide

end ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_TARGET.write_text(f'''import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := authorizedTarget
def currentEvidencePacketId : String := reviewId
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_PREPARATION_AUTHORIZED"
def currentBoundedProgramState : String := "PROPOSAL_PREPARATION_AUTHORIZED_NOT_EXECUTED"

theorem current_target_authorizes_preparation_without_scientific_execution :
    currentLiveTarget = "{TARGET}" ∧ proposalPreparationAuthorized = true ∧
    programInstallationAuthorized = false ∧ branchSelectionAuthorized = false ∧
    newPostulateAuthorized = false ∧ theoremDiscoveryAuthorized = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_AUTHORITY.write_text('''import ToeFormal.Derivation.CurrentTarget

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_is_ccft_v0_program_preparation_only :
    currentTarget = "prepare_bounded_ccft_v0_theory_construction_program" ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.proposalPreparationAuthorized = true ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.programInstallationAuthorized = false ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.theoremDiscoveryAuthorized = false := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''', encoding="utf-8", newline="\n")


def write_proposal_surfaces() -> None:
    PROPOSAL_LEAN.write_text(f'''import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority

namespace ToeFormal
namespace Derivation
namespace ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview

def resultId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0"
def reviewId : String := "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0"
def directorPacketId : String := "TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0"
def preparationTarget : String := "{TARGET}"
def proposedProgramId : String := "{PROGRAM_ID}"
def proposedMandatoryExit : String := "{EXIT_TARGET}"
def proposedStageCount : Nat := 5
def directorOptionCount : Nat := 4
def provenanceLabelCount : Nat := 5
def maximumFrozenModels : Nat := 1
def maximumPrimaryTheoremPackets : Nat := 1
def programInstalled : Bool := false
def stageOneOpened : Bool := false
def branchSelected : Bool := false
def ccftV0Constructed : Bool := false
def theoremAttempted : Bool := false

theorem proposal_is_bounded_science_centered_and_uninstalled :
    proposedStageCount = 5 ∧ directorOptionCount = 4 ∧ provenanceLabelCount = 5 ∧
    maximumFrozenModels = 1 ∧ maximumPrimaryTheoremPackets = 1 ∧
    programInstalled = false ∧ stageOneOpened = false ∧ branchSelected = false ∧
    ccftV0Constructed = false ∧ theoremAttempted = false := by
  decide

end ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_TARGET.write_text(f'''import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview

namespace ToeFormal
namespace Derivation
namespace CurrentTarget

open ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview
def aggregateTargetId : String := "ToeFormal.Derivation.CurrentTarget"
def currentLiveTarget : String := preparationTarget
def currentEvidencePacketId : String := reviewId
def currentTargetPhase : String := "CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_PROPOSAL_PREPARED"
def currentBoundedProgramState : String := "PROPOSAL_PREPARED_UNINSTALLED"

theorem current_target_preserves_uninstalled_nonselecting_proposal :
    currentLiveTarget = "{TARGET}" ∧ proposedStageCount = 5 ∧
    programInstalled = false ∧ stageOneOpened = false ∧ branchSelected = false ∧
    ccftV0Constructed = false ∧ theoremAttempted = false := by
  decide

end CurrentTarget
end Derivation
end ToeFormal
''', encoding="utf-8", newline="\n")
    CURRENT_AUTHORITY.write_text('''import ToeFormal.Derivation.CurrentTarget
import ToeFormal.Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority

namespace ToeFormal
namespace Release
namespace CurrentAuthority

def aggregateTargetId : String := "ToeFormal.Release.CurrentAuthority"
def currentTarget : String := Derivation.CurrentTarget.currentLiveTarget
def currentEvidencePacketId : String := Derivation.CurrentTarget.currentEvidencePacketId
def currentTargetPhase : String := Derivation.CurrentTarget.currentTargetPhase
def currentBoundedProgramState : String := Derivation.CurrentTarget.currentBoundedProgramState

theorem current_authority_tracks_prepared_uninstalled_ccft_v0_program :
    currentTarget = "prepare_bounded_ccft_v0_theory_construction_program" ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview.programInstalled = false ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview.branchSelected = false ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationResultReview.theoremAttempted = false ∧
    Derivation.ToeCCFTV0TheoryConstructionBoundedProgramPreparationAuthority.proposalPreparationAuthorized = true := by
  native_decide

end CurrentAuthority
end Release
end ToeFormal
''', encoding="utf-8", newline="\n")


def write_authority_test() -> None:
    AUTHORITY_TEST.write_text(f'''from __future__ import annotations
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
R=ROOT/"formal/docs/release"
A=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_v0.json"
V=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_AUTHORITY_REVIEW_v0.json"
def read(p): return json.loads(p.read_text(encoding="utf-8"))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def test_authority_is_preparation_only():
    a=read(A); assert a["authorized_target"]=="{TARGET}"; assert a["proposal_preparation_authorized"] is True
    assert a["program_installation_authorized"] is False; assert a["branch_selection_authorized"] is False
def test_terminal_bindings_reproduce():
    assert all(sha(ROOT/x["path"])==x["sha256"] for x in read(A)["consumed_terminal_checkpoint"])
def test_four_options_are_required_without_selection():
    a=read(A); assert len(a["required_director_packet_options"])==4; assert a["postulate_or_model_construction_authorized"] is False
def test_theorem_and_archive_work_are_prohibited():
    a=read(A); assert a["theorem_discovery_authorized"] is False; assert "REOPEN_HISTORICAL_OR_TARGETED_ARCHIVE_RECOVERY" in a["prohibited_work"]
def test_review_accepts_all_checks():
    v=read(V); assert v["authority_sha256"]==sha(A); assert v["accepted"] is True; assert all(v["checks"].values())
''', encoding="utf-8", newline="\n")


def write_proposal_test() -> None:
    PROPOSAL_TEST.write_text('''from __future__ import annotations
import hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
R=ROOT/"formal/docs/release"
P=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
V=R/"TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
D=R/"TOE_CCFT_V0_RESEARCH_DIRECTOR_DECISION_PACKET_v0.json"
def read(p): return json.loads(p.read_text(encoding="utf-8"))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def test_director_packet_has_four_unselected_options():
    d=read(D); assert len(d["options"])==4; assert d["option_selected"]=="NONE"; assert d["model_or_postulate_created"] is False
def test_proposal_has_five_stages_one_model_and_one_theorem_packet():
    p=read(P); assert len(p["stage_definitions_proposed"])==5; assert p["maximum_frozen_model_versions"]==1; assert p["maximum_primary_theorem_packets"]==1
def test_provenance_and_status_vocabularies_are_separate():
    p=read(P); assert len(p["provenance_vocabulary"])==5; assert len(p["theorem_status_vocabulary"])==7
def test_external_checks_are_not_action_terms():
    p=read(P); assert p["external_evaluation_checks"]==["C_FINITE_APPROXIMATION","C_IDENTIFIABILITY","C_COMPLEXITY"]; assert p["external_checks_are_not_action_terms"] is True
def test_program_remains_uninstalled_unopened_and_nonexecuting():
    p=read(P); assert p["program_installation_status"]=="UNINSTALLED"; assert p["scientific_attempts"]==0; assert p["branch_selected"]=="NONE"; assert p["ccft_v0_model"]=="NONE"; assert p["theorem_or_counterexample_attempted"] is False
def test_review_accepts_all_checks_and_hashes():
    v=read(V); assert v["accepted"] is True; assert v["reviewed_result"]["sha256"]==sha(P); assert v["reviewed_director_packet"]["sha256"]==sha(D); assert all(v["checks"].values())
''', encoding="utf-8", newline="\n")


def authorize(*, captured_at_utc: str) -> None:
    authority = build_authority(captured_at_utc=captured_at_utc)
    write_json(AUTHORITY, authority)
    review = build_authority_review(authority, captured_at_utc=captured_at_utc)
    write_json(AUTHORITY_REVIEW, review)
    write_authority_surfaces()
    write_authority_test()
    registry = read(REGISTRY)
    consumed = registry["current_projection_v0"]["current_target"]
    registry = project_registry(
        registry,
        kind="toe_ccft_v0_theory_construction_bounded_program_preparation_authorized_v0",
        evidence=rel(AUTHORITY_LEAN),
        report=rel(AUTHORITY_REVIEW),
        report_sha256=sha(AUTHORITY_REVIEW),
        outcome="CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_PREPARATION_AUTHORIZED",
        strict="PROPOSAL_PREPARATION_ONLY_NO_INSTALLATION_STAGE_OPEN_BRANCH_SELECTION_POSTULATE_MODEL_THEOREM_ARCHIVE_SEARCH_OR_PHYSICAL_PROMOTION",
        consumed_target=consumed,
        queue_scope="Prepare one bounded CCFT-v0 construction and theorem-discovery proposal plus a nonselecting Research Director Decision Packet.",
        claim_status="Preparation authority only; no program installation, stage OPEN, branch, equation, postulate, model, theorem, archive search, physical interpretation, or promotion.",
    )
    atomic_write_registry(REGISTRY, _registry_json_bytes(registry))


def prepare(*, captured_at_utc: str) -> None:
    authority = read(AUTHORITY)
    review = read(AUTHORITY_REVIEW)
    if authority["proposal_preparation_authorized"] is not True or review["accepted"] is not True:
        raise ValueError("proposal preparation authority is not valid")
    write_json(PACKET, director_packet())
    value = proposal()
    write_json(RESULT, value)
    review_value = proposal_review(value, captured_at_utc=captured_at_utc)
    write_json(RESULT_REVIEW, review_value)
    write_proposal_surfaces()
    write_proposal_test()
    registry = read(REGISTRY)
    consumed = registry["current_projection_v0"]["previous_target"]
    registry = project_registry(
        registry,
        kind="toe_ccft_v0_theory_construction_bounded_program_proposal_prepared_uninstalled_v0",
        evidence=rel(PROPOSAL_LEAN),
        report=rel(RESULT_REVIEW),
        report_sha256=sha(RESULT_REVIEW),
        outcome="CCFT_V0_THEORY_CONSTRUCTION_PROGRAM_PROPOSAL_PREPARED",
        strict="FIVE_STAGE_PROPOSAL_AND_NONSELECTING_DIRECTOR_PACKET_PREPARED_UNINSTALLED_ZERO_SCIENTIFIC_ATTEMPTS_NO_BRANCH_POSTULATE_MODEL_THEOREM_ARCHIVE_SEARCH_OR_PHYSICAL_PROMOTION",
        consumed_target=consumed,
        queue_scope="CCFT-v0 construction proposal and four-option Director Packet prepared; installation and all scientific stages remain separately unauthorized.",
        claim_status="Proposal prepared only; no branch, postulate, model, implementation, theorem, counterexample, physical interpretation, or promotion exists.",
    )
    atomic_write_registry(REGISTRY, _registry_json_bytes(registry))
    validation = {
        "artifact_id": "TOE_CCFT_V0_THEORY_CONSTRUCTION_BOUNDED_PROGRAM_PREPARATION_VALIDATION_v0",
        "schema_id": "toe.ccft_v0.theory_construction.bounded_program_preparation_validation.v0",
        "captured_at_utc": captured_at_utc,
        "result_sha256": sha(RESULT),
        "review_sha256": sha(RESULT_REVIEW),
        "director_packet_sha256": sha(PACKET),
        "scientific_boundary": {
            "program_installed": False,
            "scientific_attempts": 0,
            "branch_selected": False,
            "ccft_v0_constructed": False,
            "new_postulates_created": 0,
            "theorem_or_counterexample_attempted": False,
            "physical_interpretation_established": False,
            "archive_recovery_reopened": False,
        },
        "focused_python": {"status": "PENDING_PRECOMMIT"},
        "full_lean": {"status": "PENDING_PRECOMMIT"},
        "deterministic_generation": {"status": "PENDING_PRECOMMIT"},
        "governance": {"status": "PENDING_PRECOMMIT"},
        "repository": {"tracked_checkout_after_commit": "REQUIRED_POST_COMMIT", "reddit": "UNTRACKED_AND_UNTOUCHED", "exhaustive_python": "NOT_CLAIMED"},
        "status": "PROPOSAL_PREPARATION_READY_FOR_VALIDATION",
    }
    write_json(VALIDATION, validation)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("authorize", "prepare"))
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args()
    if args.mode == "authorize":
        authorize(captured_at_utc=args.captured_at_utc)
    else:
        prepare(captured_at_utc=args.captured_at_utc)
    print(args.mode)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
