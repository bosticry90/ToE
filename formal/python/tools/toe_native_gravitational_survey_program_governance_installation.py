"""Install the bounded gravitational-requirements survey without opening it."""

from __future__ import annotations

import subprocess
from pathlib import Path
from typing import Any

from formal.python.tools import bounded_program_governance as governance
from formal.python.tools.loop_control_registry_integrity import (
    atomic_write_registry,
)


REPO_ROOT = governance.REPO_ROOT
PROGRAM_ID = governance.GRAVITATIONAL_SURVEY_PROGRAM_ID
MANIFEST_RELATIVE_PATH = governance.PROGRAM_MANIFEST_PATHS[PROGRAM_ID]
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
INSTALLATION_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_"
    "SURVEY_PROGRAM_GOVERNANCE_INSTALLATION_v0.json"
)
INSTALLATION_PATH = REPO_ROOT / INSTALLATION_RELATIVE_PATH

INSTALLATION_COMMIT_EXACT_PATH_SET = [
    "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
    INSTALLATION_RELATIVE_PATH,
    MANIFEST_RELATIVE_PATH,
    "formal/python/tests/"
    "test_toe_native_gravitational_requirements_and_candidate_action_"
    "family_survey_program_governance_installation.py",
    "formal/python/tools/bounded_program_governance.py",
    "formal/python/tools/"
    "toe_native_gravitational_survey_program_governance_installation.py",
    "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
    "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
    "formal/toe_formal/ToeFormal/Release/"
    "ToeNativeGravitationalRequirementsAndCandidateActionFamilySurvey"
    "ProgramGovernanceInstallationV0.lean",
    "formal/toe_formal/ToeFormalAll.lean",
]

COMMON_AUTHORIZED_INPUTS = [
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v0",
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_REVIEW_20260718_v0",
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_REVIEW_20260718_v2",
    "TOE_POST_CENSUS_NATIVE_FRONTIER_DECISION_RESULT_v0",
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_BOUNDED_CLOSEOUT_RESULT_v0",
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
]

COMMON_PROHIBITED_CLAIMS = [
    "gravitational action adoption",
    "native gravitational principle derivation",
    "standard GR selection or promotion",
    "quadratic gravity promotion from reference control",
    "canonical evidence promotion",
    "master action promotion",
    "gravitational calculation",
    "automatic successor authorization",
]

STAGES = [
    {
        "stage_number": 1,
        "semantic_stage_id": "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY",
        "canonical_target": "inventory_toe_native_gravitational_requirements_v0",
        "normalized_scientific_question": (
            "What do the ten preserved native-gravity requirement rows state, "
            "what authority and statement class does each possess, and which "
            "definitions, conflicts, or derivations remain missing?"
        ),
        "required_outputs": [
            "ten_row_source_and_authority_ledger",
            "statement_class_for_every_requirement",
            "requirement_scope_units_symmetry_and_selection_power_ledger",
            "conflict_supersession_and_missing_definition_ledger",
        ],
        "stage_prohibited_claims": [
            "requirement truth or native status from historical wording alone",
            "action-family compatibility judgment",
            "new gravitational postulate",
        ],
        "terminal_outcomes": [
            "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY_COMPLETE",
            "NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY_COMPLETE_WITH_CONFLICTS",
            "NATIVE_GRAVITATIONAL_REQUIREMENT_EVIDENCE_INSUFFICIENT",
        ],
        "stem": "TOE_NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY",
        "tool": "toe_native_gravitational_requirement_inventory_stage_authorization.py",
        "lean_open": "ToeNativeGravitationalRequirementInventoryAttemptOpen",
        "lean_result": "ToeNativeGravitationalRequirementInventoryResult",
    },
    {
        "stage_number": 2,
        "semantic_stage_id": "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY",
        "canonical_target": "inventory_toe_candidate_gravitational_action_families_v0",
        "normalized_scientific_question": (
            "What are the exact source-bound field content, action terms, "
            "derivative order, symmetries, coefficients, limits, calculations, "
            "negative results, and historical roles of the seven preserved "
            "candidate gravitational action families?"
        ),
        "required_outputs": [
            "seven_family_source_and_lineage_ledger",
            "field_content_action_terms_derivative_order_and_symmetry_ledger",
            "coefficient_origin_limits_calculations_and_negative_result_ledger",
            "native_control_historical_superseded_and_scope_classification",
        ],
        "stage_prohibited_claims": [
            "family viability or superiority judgment",
            "outside-scope family scientific refutation",
            "family-envelope expansion",
        ],
        "terminal_outcomes": [
            "CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY_COMPLETE",
            "ACTION_FAMILY_INVENTORY_COMPLETE_WITH_UNRESOLVED_MEANINGS",
            "ACTION_FAMILY_SOURCE_EVIDENCE_INSUFFICIENT",
        ],
        "stem": "TOE_CANDIDATE_GRAVITATIONAL_ACTION_FAMILY_INVENTORY",
        "tool": "toe_candidate_gravitational_action_family_inventory_stage_authorization.py",
        "lean_open": "ToeCandidateGravitationalActionFamilyInventoryAttemptOpen",
        "lean_result": "ToeCandidateGravitationalActionFamilyInventoryResult",
    },
    {
        "stage_number": 3,
        "semantic_stage_id": (
            "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION"
        ),
        "canonical_target": (
            "reconstruct_toe_gravitational_requirement_and_action_family_"
            "lineages_v0"
        ),
        "normalized_scientific_question": (
            "How do the source-bound gravitational requirements and action "
            "families descend, branch, conflict, supersede, or remain "
            "documentarily unresolved?"
        ),
        "required_outputs": [
            "requirement_lineage_graph",
            "action_family_lineage_graph",
            "source_to_review_and_source_to_result_edges",
            "supersession_conflict_and_unresolved_relationship_ledger",
        ],
        "stage_prohibited_claims": [
            "scientific truth from documentary descent",
            "silent supersession",
            "semantic equivalence from symbol similarity",
            "compatibility judgment",
        ],
        "terminal_outcomes": [
            "GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGES_RECONSTRUCTED",
            "LINEAGES_RECONSTRUCTED_WITH_BOUNDED_UNRESOLVED_RELATIONSHIPS",
            "LINEAGE_RECONSTRUCTION_BLOCKED_BY_PROVENANCE",
        ],
        "stem": "TOE_GRAVITATIONAL_REQUIREMENT_AND_FAMILY_LINEAGE_RECONSTRUCTION",
        "tool": (
            "toe_gravitational_requirement_and_action_family_lineage_"
            "reconstruction_stage_authorization.py"
        ),
        "lean_open": (
            "ToeGravitationalRequirementAndActionFamilyLineage"
            "ReconstructionAttemptOpen"
        ),
        "lean_result": (
            "ToeGravitationalRequirementAndActionFamilyLineage"
            "ReconstructionResult"
        ),
    },
    {
        "stage_number": 4,
        "semantic_stage_id": "SOURCE_BOUND_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY",
        "canonical_target": (
            "survey_toe_source_bound_gravitational_requirement_family_"
            "compatibility_v0"
        ),
        "normalized_scientific_question": (
            "What provisional compatibility status does each of the bounded "
            "ten-by-seven requirement-family cells receive when every "
            "non-unresolved judgment is tied to independently reviewable source "
            "evidence?"
        ),
        "required_outputs": [
            "bounded_ten_by_seven_provisional_compatibility_survey",
            "source_excerpt_and_domain_binding_for_every_non_unresolved_cell",
            "independent_cell_review",
            "uncertainty_conflict_and_missing_derivation_ledger",
            "standard_GR_oracle_isolation_audit",
        ],
        "stage_prohibited_claims": [
            "population of the closed V2 automated matrix",
            "self-attested scientific evidence",
            "survivor-set or native-principle verdict",
        ],
        "terminal_outcomes": [
            "SOURCE_BOUND_COMPATIBILITY_SURVEY_COMPLETE",
            "COMPATIBILITY_SURVEY_COMPLETE_WITH_UNRESOLVED_CELLS",
            "COMPATIBILITY_SURVEY_BLOCKED_BY_SOURCE_EVIDENCE",
        ],
        "stem": "TOE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY",
        "tool": (
            "toe_source_bound_gravitational_requirement_family_"
            "compatibility_survey_stage_authorization.py"
        ),
        "lean_open": (
            "ToeSourceBoundGravitationalRequirementFamilyCompatibility"
            "SurveyAttemptOpen"
        ),
        "lean_result": (
            "ToeSourceBoundGravitationalRequirementFamilyCompatibility"
            "SurveyResult"
        ),
    },
    {
        "stage_number": 5,
        "semantic_stage_id": "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF",
        "canonical_target": (
            "select_toe_gravitational_action_family_eligibility_handoff_v0"
        ),
        "normalized_scientific_question": (
            "Which preserved candidate action families, if any, are eligible "
            "for a separately authorized bounded action-selection adjudication, "
            "and what exact definitions, derivations, conflicts, or evidence "
            "still block the others?"
        ),
        "required_outputs": [
            "eligibility_classification_for_all_seven_families",
            "remaining_definition_derivation_conflict_and_evidence_ledger",
            "exactly_one_program_terminal_outcome",
            "separately_authorizable_action_selection_handoff_or_explicit_no_handoff",
        ],
        "stage_prohibited_claims": [
            "gravitational action adoption",
            "native gravitational principle derivation",
            "automatic action-selection program",
            "standard GR promotion",
            "empirical validation",
        ],
        "terminal_outcomes": [
            "ONE_OR_MORE_ACTION_FAMILIES_READY_FOR_SELECTION",
            "ALL_CANDIDATES_REQUIRE_ONE_DEFINITION",
            "ALL_CANDIDATES_REQUIRE_ONE_DERIVATION",
            "NO_PRESERVED_CANDIDATE_SATISFIES_NATIVE_REQUIREMENTS",
            "GRAVITATIONAL_REQUIREMENTS_CONFLICT",
            "SOURCE_EVIDENCE_INSUFFICIENT",
        ],
        "stem": "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF",
        "tool": "toe_gravitational_action_family_eligibility_handoff_stage_authorization.py",
        "lean_open": "ToeGravitationalActionFamilyEligibilityHandoffAttemptOpen",
        "lean_result": "ToeGravitationalActionFamilyEligibilityHandoffResult",
    },
]


def _git_head() -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _event_path(attempt: int, event_type: str) -> str:
    return (
        "formal/docs/release/bounded_program_events/"
        f"{PROGRAM_ID}_ATTEMPT_{attempt:02d}_{event_type}_v0.json"
    )


def _stage_manifest(row: dict[str, Any]) -> dict[str, Any]:
    attempt = row["stage_number"]
    stem = row["stem"]
    scope = {
        "semantic_stage_id": row["semantic_stage_id"],
        "normalized_scientific_question": row["normalized_scientific_question"],
        "authorized_inputs": COMMON_AUTHORIZED_INPUTS,
        "required_outputs": row["required_outputs"],
        "prohibited_claims": list(
            dict.fromkeys(
                COMMON_PROHIBITED_CLAIMS + row["stage_prohibited_claims"]
            )
        ),
        "dependency_artifact_ids": (
            [
                "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
                "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
            ]
            if attempt == 1
            else [STAGES[attempt - 2]["semantic_stage_id"]]
        ),
        "terminal_outcome_vocabulary": row["terminal_outcomes"],
    }
    open_event = _event_path(attempt, "OPEN")
    close_event = _event_path(attempt, "CLOSE")
    open_paths = [
        "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        f"formal/docs/release/{stem}_OPEN_VALIDATION_v0.json",
        open_event,
        f"formal/python/tools/{row['tool']}",
        "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
        f"formal/toe_formal/ToeFormal/Derivation/{row['lean_open']}.lean",
        "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
        "formal/toe_formal/ToeFormalAll.lean",
    ]
    result_path = f"formal/docs/release/{stem}_RESULT_v0.json"
    review_path = f"formal/docs/release/{stem}_RESULT_REVIEW_v0.json"
    close_paths = [
        "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        review_path,
        result_path,
        f"formal/docs/release/{stem}_VALIDATION_v0.json",
        close_event,
        "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
        f"formal/toe_formal/ToeFormal/Derivation/{row['lean_result']}.lean",
        "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
        "formal/toe_formal/ToeFormalAll.lean",
    ]
    return {
        "canonical_scope": scope,
        "canonical_scope_hash": governance.scope_hash(scope),
        "canonical_target": row["canonical_target"],
        "conditional": attempt != 1,
        "mandatory_terminal_outcomes": row["terminal_outcomes"],
        "prospective_envelope": {
            "close_commit_exact_path_set": sorted(close_paths),
            "close_event_path": close_event,
            "open_commit_exact_path_set": sorted(open_paths),
            "open_event_path": open_event,
            "result_artifact_path": result_path,
            "review_artifact_path": review_path,
        },
        "semantic_stage_id": row["semantic_stage_id"],
        "stage_number": attempt,
    }


def build_manifest(installed_from_commit: str) -> dict[str, Any]:
    terminal_outcomes = STAGES[-1]["terminal_outcomes"]
    manifest: dict[str, Any] = {
        "authorized_stage_count": 5,
        "installation_envelope": {
            "commit_exact_path_set": sorted(INSTALLATION_COMMIT_EXACT_PATH_SET),
            "installed_from_commit": installed_from_commit,
        },
        "mandatory_exit": {
            "target": (
                "close_toe_native_gravitational_requirements_and_candidate_"
                "action_family_survey_v0_after_bounded_result_v0"
            ),
            "terminal_outcomes": terminal_outcomes,
        },
        "manifest_hash": "",
        "manifest_mode": "PROSPECTIVE_STATIC",
        "native_hypothesis_tested": (
            "HYP_TOE_NATIVE_GRAVITATIONAL_PRINCIPLE_ACTION_SELECTION_v0"
        ),
        "native_relevance": {
            "kind": "ONE_PREREQUISITE_FROM_NATIVE_CALCULATION",
            "statement": (
                "Surveys source-bound native gravitational requirements and "
                "seven preserved action families before any action-selection "
                "adjudication or gravitational calculation."
            ),
        },
        "no_subsidiary_scientific_targets": True,
        "program_id": PROGRAM_ID,
        "program_terminal_outcomes": terminal_outcomes,
        "repair_attempt_count": 0,
        "schema_id": "toe.bounded_program.immutable_manifest.v1",
        "stages": [_stage_manifest(row) for row in STAGES],
        "status": "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST",
        "workload_caps": {
            "maximum_action_families": 7,
            "maximum_compatibility_cells": 70,
            "maximum_evidence_references_per_cell": 8,
            "maximum_extracted_evidence_statements": 512,
            "maximum_lineage_components": 32,
            "maximum_native_requirement_rows": 10,
            "maximum_source_artifacts_for_deep_review": 96,
            "maximum_total_bounded_source_excerpt_words": 24000,
            "maximum_unresolved_lineage_relationships": 32,
        },
    }
    manifest["manifest_hash"] = governance._hashed_payload(
        manifest, "manifest_hash"
    )
    return manifest


def build_installation(
    *, installed_from_commit: str, manifest: dict[str, Any]
) -> dict[str, Any]:
    return {
        "artifact_id": (
            "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_"
            "FAMILY_SURVEY_PROGRAM_GOVERNANCE_INSTALLATION_v0"
        ),
        "attempted_stage_count": 0,
        "authorized_stage_count": 5,
        "candidate_action_family_count": 7,
        "captured_at_utc": "2026-07-31T12:00:00Z",
        "compatibility_cells_created": 0,
        "evidence_promoted": False,
        "gravitational_action_selected": False,
        "gravitational_calculation_started": False,
        "installed_from_commit": installed_from_commit,
        "installed_program_state": "UNOPENED",
        "installation_authority": (
            "AUTHORIZE_GRAVITATIONAL_SURVEY_PROGRAM_INSTALLATION"
        ),
        "manifest_hash": manifest["manifest_hash"],
        "manifest_path": MANIFEST_RELATIVE_PATH,
        "mandatory_exit_target": manifest["mandatory_exit"]["target"],
        "native_gravitational_principle_selected": False,
        "no_subsidiary_scientific_targets": True,
        "preserved_scientific_target": (
            governance.GRAVITATIONAL_SURVEY_PREPARATION_TARGET
        ),
        "program_id": PROGRAM_ID,
        "repair_attempt_count": 0,
        "schema_id": (
            "toe.native_gravitational_requirements_and_candidate_action_"
            "family_survey.program_governance_installation.v0"
        ),
        "scientific_execution_authorized": False,
        "scientific_output_created": False,
        "stage_1_opened": False,
        "status": (
            "PROGRAM_GOVERNANCE_INSTALLED_UNOPENED_NO_SCIENTIFIC_ROTATION"
        ),
    }


def main() -> int:
    if MANIFEST_PATH.exists() or INSTALLATION_PATH.exists():
        raise governance.BoundedProgramError(
            "gravitational survey installation artifacts already exist"
        )
    installed_from_commit = _git_head()
    manifest = build_manifest(installed_from_commit)
    governance.validate_ijson(manifest)
    MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST_PATH.write_bytes(governance._pretty_json_bytes(manifest))

    registry = governance.strict_json_load(governance.REGISTRY_PATH)
    migrated = governance.install_gravitational_survey_program(registry)
    governance.validate_registry_extension(migrated)
    atomic_write_registry(
        governance.REGISTRY_PATH, governance._registry_json_bytes(migrated)
    )

    installation = build_installation(
        installed_from_commit=installed_from_commit, manifest=manifest
    )
    INSTALLATION_PATH.write_bytes(governance._pretty_json_bytes(installation))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
