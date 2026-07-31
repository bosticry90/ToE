"""Install the bounded CCFT mathematical-core program unopened."""

from __future__ import annotations

import subprocess
from typing import Any

from formal.python.tools import bounded_program_governance as governance
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry


REPO_ROOT = governance.REPO_ROOT
PROGRAM_ID = governance.CCFT_CORE_PROGRAM_ID
MANIFEST_RELATIVE_PATH = governance.PROGRAM_MANIFEST_PATHS[PROGRAM_ID]
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
PREPARATION_RESULT_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_"
    "BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
)
PREPARATION_RESULT_PATH = REPO_ROOT / PREPARATION_RESULT_RELATIVE_PATH
INSTALLATION_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_"
    "PROGRAM_GOVERNANCE_INSTALLATION_v0.json"
)
INSTALLATION_PATH = REPO_ROOT / INSTALLATION_RELATIVE_PATH

INSTALLATION_COMMIT_EXACT_PATH_SET = [
    "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
    INSTALLATION_RELATIVE_PATH,
    MANIFEST_RELATIVE_PATH,
    "formal/python/tests/"
    "test_toe_ccft_core_program_governance_installation.py",
    "formal/python/tools/bounded_program_governance.py",
    "formal/python/tools/toe_ccft_core_program_governance_installation.py",
    "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
    "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
    "formal/toe_formal/ToeFormal/Release/"
    "ToeCCFTCoreProgramGovernanceInstallationV0.lean",
    "formal/toe_formal/ToeFormalAll.lean",
]

COMMON_AUTHORIZED_INPUTS = [
    "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
    "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
    "TOE_CCFT_PRIMARY_NATIVE_POSITIVE_CONTENT_FRONTIER_SELECTION_RESULT_v0",
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_BOUNDED_CLOSEOUT_RESULT_v0",
    "TOE_NATIVE_HYPOTHESIS_SOURCE_LINEAGE_RECONSTRUCTION_RESULT_v0",
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_CLAIM_EXTRACTION_RESULT_v0",
    "TOE_CURRENT_NATIVE_HYPOTHESIS_EVIDENCE_RECONCILIATION_RESULT_v0",
    "TOE_NATIVE_CONTROLLED_COHERENCE_CLAIM_INVENTORY_RESULT_20260729_v0",
    "TOE_NATIVE_COHERENCE_OPERATIONAL_DEFINITION_RESULT_20260729_v0",
    "CALC-TOE-NATIVE-COHERENCE-ONTOLOGY-AND-REPRESENTATION-V0-BOUNDED-CLOSEOUT-v0",
]

COMMON_PROHIBITED_CLAIMS = [
    "CCFT validation or empirical confirmation",
    "coherence declared fundamental or physically real",
    "real scalar or any other representation assumed in advance",
    "CCFT action or evolution law construction outside a passed core decision",
    "matter gravity or scale seam selection",
    "observable or discriminator derivation",
    "master action promotion or QFT-gravity closure",
    "canonical evidence promotion",
    "automatic successor authorization",
]

STAGE_METADATA = [
    {
        "semantic_stage_id": "CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY",
        "target": "inventory_toe_source_bound_ccft_mathematical_structures_v0",
        "question": (
            "What explicit source-bound CCFT variables, equations, operators, "
            "domains, data, units, conservation relations, calculations, and "
            "missing definitions occur in the deterministically selected evidence?"
        ),
        "stem": "TOE_CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY",
        "tool": "toe_ccft_source_bound_mathematical_inventory_stage_authorization.py",
        "lean_open": "ToeCCFTSourceBoundMathematicalInventoryAttemptOpen",
        "lean_result": "ToeCCFTSourceBoundMathematicalInventoryResult",
    },
    {
        "semantic_stage_id": "CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION",
        "target": "reconstruct_toe_ccft_mathematical_lineages_and_conflicts_v0",
        "question": (
            "How do the inventoried CCFT mathematical formulations descend, "
            "revise, conflict, change symbol meaning, or remain unresolved?"
        ),
        "stem": "TOE_CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION",
        "tool": "toe_ccft_mathematical_lineage_and_conflict_reconciliation_stage_authorization.py",
        "lean_open": "ToeCCFTMathematicalLineageAndConflictReconciliationAttemptOpen",
        "lean_result": "ToeCCFTMathematicalLineageAndConflictReconciliationResult",
    },
    {
        "semantic_stage_id": "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION",
        "target": "operationalize_toe_retained_ccft_mathematical_objects_v0",
        "question": (
            "Can each retained CCFT mathematical object receive a controlled "
            "physical bearer, value, zero, units, scale, operation, comparator, "
            "measurement channel, and adequacy-failure condition?"
        ),
        "stem": "TOE_CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION",
        "tool": "toe_ccft_mathematical_object_operationalization_stage_authorization.py",
        "lean_open": "ToeCCFTMathematicalObjectOperationalizationAttemptOpen",
        "lean_result": "ToeCCFTMathematicalObjectOperationalizationResult",
    },
    {
        "semantic_stage_id": "MINIMAL_CLOSED_CCFT_CORE_DECISION",
        "target": "select_or_reject_toe_minimal_closed_ccft_core_v0",
        "question": (
            "Does a smallest retained CCFT system close its state, evolution, "
            "exchange, data, scale, interpretation, and operational-output contract "
            "without inventing missing physics?"
        ),
        "stem": "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION",
        "tool": "toe_minimal_closed_ccft_core_decision_stage_authorization.py",
        "lean_open": "ToeMinimalClosedCCFTCoreDecisionAttemptOpen",
        "lean_result": "ToeMinimalClosedCCFTCoreDecisionResult",
    },
    {
        "semantic_stage_id": "CCFT_VIABILITY_TEST_HANDOFF_DECISION",
        "target": "select_toe_ccft_core_viability_testing_handoff_v0",
        "question": (
            "What exact terminal outcome follows from the core decision, and is "
            "a separately authorized internal-viability program preparation "
            "handoff justified without opening it automatically?"
        ),
        "stem": "TOE_CCFT_VIABILITY_TEST_HANDOFF_DECISION",
        "tool": "toe_ccft_viability_test_handoff_decision_stage_authorization.py",
        "lean_open": "ToeCCFTViabilityTestHandoffDecisionAttemptOpen",
        "lean_result": "ToeCCFTViabilityTestHandoffDecisionResult",
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


def _stage_manifest(
    row: dict[str, Any], prepared_stage: dict[str, Any]
) -> dict[str, Any]:
    attempt = prepared_stage["stage_number"]
    scope = {
        "semantic_stage_id": row["semantic_stage_id"],
        "normalized_scientific_question": row["question"],
        "authorized_inputs": COMMON_AUTHORIZED_INPUTS,
        "required_outputs": prepared_stage["required_outputs"],
        "prohibited_claims": list(
            dict.fromkeys(COMMON_PROHIBITED_CLAIMS + prepared_stage["prohibited_claims"])
        ),
        "dependency_artifact_ids": (
            [
                "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
                "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
            ]
            if attempt == 1
            else [STAGE_METADATA[attempt - 2]["semantic_stage_id"]]
        ),
        "terminal_outcome_vocabulary": prepared_stage["terminal_outcomes"],
    }
    stem = row["stem"]
    open_event = _event_path(attempt, "OPEN")
    close_event = _event_path(attempt, "CLOSE")
    result_path = f"formal/docs/release/{stem}_RESULT_v0.json"
    review_path = f"formal/docs/release/{stem}_RESULT_REVIEW_v0.json"
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
        "canonical_target": row["target"],
        "conditional": attempt != 1,
        "mandatory_terminal_outcomes": prepared_stage["terminal_outcomes"],
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
    prepared = governance.strict_json_load(PREPARATION_RESULT_PATH)
    prepared_stages = prepared["stages"]
    if [row["semantic_stage_id"] for row in prepared_stages] != [
        row["semantic_stage_id"] for row in STAGE_METADATA
    ]:
        raise governance.BoundedProgramError(
            "prepared stages do not match CCFT installation metadata"
        )
    controls = prepared["program_controls"]
    workload_caps = {
        key: value for key, value in controls.items() if key.startswith("maximum_")
    }
    manifest: dict[str, Any] = {
        "authorized_stage_count": 5,
        "deep_review_selection_contract": prepared["deep_review_selection_contract"],
        "installation_envelope": {
            "commit_exact_path_set": sorted(INSTALLATION_COMMIT_EXACT_PATH_SET),
            "installed_from_commit": installed_from_commit,
        },
        "mandatory_exit": {
            "target": prepared["mandatory_exit_target_proposed"],
            "terminal_outcomes": list(
                prepared["program_terminal_outcome_lifecycle_mapping"]
            )[:-1],
        },
        "manifest_hash": "",
        "manifest_mode": "PROSPECTIVE_STATIC",
        "mathematical_content_vocabulary": prepared["mathematical_content_vocabulary"],
        "native_hypothesis_tested": prepared["selected_frontier"]["hypothesis_id"],
        "native_relevance": {
            "kind": "DIRECT_NATIVE_TEST",
            "statement": (
                "Tests whether the broader source-bound CCFT evidence supplies a "
                "recoverable, operationalizable, minimal mathematical core before "
                "any field, action, seam, observable, or viability claim."
            ),
        },
        "no_subsidiary_scientific_targets": True,
        "operationalization_questions": prepared["operationalization_questions"],
        "passive_content_contract": prepared["passive_content_contract"],
        "program_id": PROGRAM_ID,
        "program_terminal_outcomes": list(
            prepared["program_terminal_outcome_lifecycle_mapping"]
        )[:-1],
        "repair_attempt_count": 0,
        "result_state_mapping": prepared[
            "program_terminal_outcome_lifecycle_mapping"
        ],
        "schema_id": "toe.bounded_program.immutable_manifest.v1",
        "source_scope_contract": prepared["source_scope_contract"],
        "stages": [
            _stage_manifest(metadata, prepared_stage)
            for metadata, prepared_stage in zip(
                STAGE_METADATA, prepared_stages, strict=True
            )
        ],
        "status": "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST",
        "workload_caps": workload_caps,
    }
    manifest["manifest_hash"] = governance._hashed_payload(manifest, "manifest_hash")
    return manifest


def build_installation(
    *, installed_from_commit: str, manifest: dict[str, Any]
) -> dict[str, Any]:
    return {
        "artifact_id": (
            "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_"
            "PROGRAM_GOVERNANCE_INSTALLATION_v0"
        ),
        "attempted_stage_count": 0,
        "authorized_stage_count": 5,
        "captured_at_utc": "2026-07-31T21:40:00Z",
        "ccft_action_or_evolution_law_constructed": False,
        "ccft_mathematical_core_recovered": False,
        "ccft_model_or_physical_claim_established": False,
        "ccft_representation_or_field_selected": False,
        "ccft_seam_observable_or_discriminator_selected": False,
        "evidence_promoted": False,
        "installed_from_commit": installed_from_commit,
        "installed_program_state": "UNOPENED",
        "installation_authority": "AUTHORIZE_CCFT_CORE_PROGRAM_INSTALLATION",
        "manifest_hash": manifest["manifest_hash"],
        "manifest_path": MANIFEST_RELATIVE_PATH,
        "mandatory_exit_target": manifest["mandatory_exit"]["target"],
        "no_subsidiary_scientific_targets": True,
        "operational_coherence_definition_established": False,
        "preserved_scientific_target": governance.CCFT_CORE_PREPARATION_TARGET,
        "program_id": PROGRAM_ID,
        "repair_attempt_count": 0,
        "schema_id": (
            "toe.ccft_native_mathematical_core_and_operationalization."
            "program_governance_installation.v0"
        ),
        "scientific_execution_authorized": False,
        "scientific_output_created": False,
        "stage_1_opened": False,
        "status": "PROGRAM_GOVERNANCE_INSTALLED_UNOPENED_NO_SCIENTIFIC_ROTATION",
    }


def main() -> int:
    if MANIFEST_PATH.exists() or INSTALLATION_PATH.exists():
        raise governance.BoundedProgramError(
            "CCFT core installation artifacts already exist"
        )
    installed_from_commit = _git_head()
    manifest = build_manifest(installed_from_commit)
    governance.validate_ijson(manifest)
    MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST_PATH.write_bytes(governance._pretty_json_bytes(manifest))

    registry = governance.strict_json_load(governance.REGISTRY_PATH)
    migrated = governance.install_ccft_core_program(registry)
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
