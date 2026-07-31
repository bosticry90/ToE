"""Install the bounded positive gravitational-principle program unopened."""

from __future__ import annotations

import subprocess
from typing import Any

from formal.python.tools import bounded_program_governance as governance
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry


REPO_ROOT = governance.REPO_ROOT
PROGRAM_ID = governance.POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID
MANIFEST_RELATIVE_PATH = governance.PROGRAM_MANIFEST_PATHS[PROGRAM_ID]
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
PREPARATION_RESULT_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_"
    "BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
)
PREPARATION_RESULT_PATH = REPO_ROOT / PREPARATION_RESULT_RELATIVE_PATH
INSTALLATION_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_"
    "PROGRAM_GOVERNANCE_INSTALLATION_v0.json"
)
INSTALLATION_PATH = REPO_ROOT / INSTALLATION_RELATIVE_PATH

INSTALLATION_COMMIT_EXACT_PATH_SET = [
    "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
    INSTALLATION_RELATIVE_PATH,
    MANIFEST_RELATIVE_PATH,
    "formal/python/tests/"
    "test_toe_positive_gravitational_principle_program_governance_"
    "installation.py",
    "formal/python/tools/bounded_program_governance.py",
    "formal/python/tools/"
    "toe_positive_gravitational_principle_program_governance_installation.py",
    "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
    "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
    "formal/toe_formal/ToeFormal/Release/"
    "ToePositiveGravitationalPrincipleProgramGovernanceInstallationV0.lean",
    "formal/toe_formal/ToeFormalAll.lean",
]

COMMON_AUTHORIZED_INPUTS = [
    "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
    "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0_BOUNDED_CLOSEOUT_RESULT_v0",
    "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_RESULT_v0",
    "TOE_SOURCE_BOUND_GRAVITATIONAL_REQUIREMENT_FAMILY_COMPATIBILITY_SURVEY_RESULT_v0",
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENT_INVENTORY_RESULT_v0",
    "TOE_CURRENT_NATIVE_HYPOTHESIS_EVIDENCE_RECONCILIATION_RESULT_v0",
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_CLAIM_EXTRACTION_RESULT_v0",
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_BOUNDED_CLOSEOUT_RESULT_v0",
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v0",
]

COMMON_PROHIBITED_CLAIMS = [
    "native gravitational principle truth before bounded derivation",
    "gravitational action construction or selection before an authorized handoff",
    "Einstein-Hilbert gravity promoted from provisional baseline to native law",
    "quadratic gravity promoted or reopened from reference control",
    "master action promotion",
    "C_k firewall treated as a physical action term",
    "canonical evidence promotion",
    "empirical validation or QFT-gravity closure",
    "automatic successor authorization",
]

STAGE_METADATA = [
    {
        "semantic_stage_id": "POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY",
        "target": "inventory_toe_positive_native_gravitational_principle_sources_v0",
        "normalized_scientific_question": (
            "Which source-bound statements in the authorized native ontology, "
            "matter-geometry, pillar-seam, emergence, conservation, master-action, "
            "and C_k domains are genuine candidates for a positive gravitational "
            "principle rather than requirements, baselines, firewalls, or heuristics?"
        ),
        "stem": "TOE_POSITIVE_GRAVITATIONAL_PRINCIPLE_SOURCE_INVENTORY",
        "tool": (
            "toe_positive_gravitational_principle_source_inventory_"
            "stage_authorization.py"
        ),
        "lean_open": "ToePositiveGravitationalPrincipleSourceInventoryAttemptOpen",
        "lean_result": "ToePositiveGravitationalPrincipleSourceInventoryResult",
    },
    {
        "semantic_stage_id": (
            "POSITIVE_PRINCIPLE_AND_EVALUATION_REQUIREMENT_DISTINCTION"
        ),
        "target": (
            "distinguish_toe_positive_gravitational_principles_from_"
            "evaluation_requirements_v0"
        ),
        "normalized_scientific_question": (
            "Do any inventoried statements provide a source-bound physical reason "
            "that constrains gravity, rather than only filtering candidate laws by "
            "consistency, known-physics recovery, or architectural exclusion?"
        ),
        "stem": "TOE_POSITIVE_PRINCIPLE_AND_EVALUATION_REQUIREMENT_DISTINCTION",
        "tool": (
            "toe_positive_principle_and_evaluation_requirement_distinction_"
            "stage_authorization.py"
        ),
        "lean_open": (
            "ToePositivePrincipleAndEvaluationRequirementDistinctionAttemptOpen"
        ),
        "lean_result": (
            "ToePositivePrincipleAndEvaluationRequirementDistinctionResult"
        ),
    },
    {
        "semantic_stage_id": (
            "POSITIVE_PRINCIPLE_GRAVITATIONAL_CONSTRAINT_POWER_TEST"
        ),
        "target": (
            "test_toe_positive_gravitational_principle_action_constraint_power_v0"
        ),
        "normalized_scientific_question": (
            "Does each surviving candidate principle nontrivially constrain the "
            "gravitational variables, symmetries, locality, derivative order, "
            "couplings, source map, degrees of freedom, action terms, or coefficient "
            "relations without adding unsupported physics?"
        ),
        "stem": "TOE_POSITIVE_PRINCIPLE_GRAVITATIONAL_CONSTRAINT_POWER_TEST",
        "tool": (
            "toe_positive_principle_gravitational_constraint_power_test_"
            "stage_authorization.py"
        ),
        "lean_open": (
            "ToePositivePrincipleGravitationalConstraintPowerTestAttemptOpen"
        ),
        "lean_result": (
            "ToePositivePrincipleGravitationalConstraintPowerTestResult"
        ),
    },
    {
        "semantic_stage_id": "PERMITTED_GRAVITATIONAL_ACTION_CLASS_DERIVATION",
        "target": (
            "derive_toe_positive_principle_permitted_gravitational_action_class_v0"
        ),
        "normalized_scientific_question": (
            "Given a passed source-bound constraint map, does the candidate "
            "principle derive a unique action, a finite family, a broad action "
            "class, exclusions only, or no usable gravitational action constraint?"
        ),
        "stem": "TOE_PERMITTED_GRAVITATIONAL_ACTION_CLASS_DERIVATION",
        "tool": (
            "toe_permitted_gravitational_action_class_derivation_"
            "stage_authorization.py"
        ),
        "lean_open": (
            "ToePermittedGravitationalActionClassDerivationAttemptOpen"
        ),
        "lean_result": "ToePermittedGravitationalActionClassDerivationResult",
    },
    {
        "semantic_stage_id": (
            "POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_HANDOFF_DECISION"
        ),
        "target": "select_toe_positive_native_gravitational_principle_handoff_v0",
        "normalized_scientific_question": (
            "What exact bounded terminal result follows from the principle and "
            "action-class analysis, and is a separately authorized action "
            "construction handoff justified without opening it automatically?"
        ),
        "stem": "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_HANDOFF_DECISION",
        "tool": (
            "toe_positive_native_gravitational_principle_handoff_decision_"
            "stage_authorization.py"
        ),
        "lean_open": (
            "ToePositiveNativeGravitationalPrincipleHandoffDecisionAttemptOpen"
        ),
        "lean_result": (
            "ToePositiveNativeGravitationalPrincipleHandoffDecisionResult"
        ),
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
        "normalized_scientific_question": row["normalized_scientific_question"],
        "authorized_inputs": COMMON_AUTHORIZED_INPUTS,
        "required_outputs": prepared_stage["required_outputs"],
        "prohibited_claims": list(
            dict.fromkeys(
                COMMON_PROHIBITED_CLAIMS + prepared_stage["prohibited_claims"]
            )
        ),
        "dependency_artifact_ids": (
            [
                "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
                "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
            ]
            if attempt == 1
            else [STAGE_METADATA[attempt - 2]["semantic_stage_id"]]
        ),
        "terminal_outcome_vocabulary": prepared_stage["terminal_outcomes"],
    }
    open_event = _event_path(attempt, "OPEN")
    close_event = _event_path(attempt, "CLOSE")
    stem = row["stem"]
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
            "prepared stages do not match installation metadata"
        )
    controls = prepared["program_controls"]
    workload_caps = {
        key: value
        for key, value in controls.items()
        if key.startswith("maximum_")
    }
    manifest: dict[str, Any] = {
        "authorized_stage_count": 5,
        "deep_review_selection_contract": prepared[
            "deep_review_selection_contract"
        ],
        "installation_envelope": {
            "commit_exact_path_set": sorted(INSTALLATION_COMMIT_EXACT_PATH_SET),
            "installed_from_commit": installed_from_commit,
        },
        "mandatory_exit": {
            "target": prepared["mandatory_exit_target_proposed"],
            "terminal_outcomes": prepared["program_terminal_outcomes"],
        },
        "manifest_hash": "",
        "manifest_mode": "PROSPECTIVE_STATIC",
        "native_hypothesis_tested": prepared["native_hypothesis"]["hypothesis_id"],
        "native_relevance": {
            "kind": "DIRECT_NATIVE_TEST",
            "statement": (
                "Tests whether the preserved native ToE architecture supplies "
                "a positive gravitational principle with nontrivial action-class "
                "constraint power before any action construction or selection."
            ),
        },
        "no_subsidiary_scientific_targets": True,
        "principle_source_domains": prepared["principle_source_domains"],
        "principle_status_vocabulary": prepared["principle_status_vocabulary"],
        "program_id": PROGRAM_ID,
        "program_terminal_outcomes": prepared["program_terminal_outcomes"],
        "repair_attempt_count": 0,
        "result_state_mapping": prepared["result_state_mapping"],
        "schema_id": "toe.bounded_program.immutable_manifest.v1",
        "stages": [
            _stage_manifest(metadata, prepared_stage)
            for metadata, prepared_stage in zip(
                STAGE_METADATA, prepared_stages, strict=True
            )
        ],
        "status": "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST",
        "workload_caps": workload_caps,
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
            "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_"
            "PROGRAM_GOVERNANCE_INSTALLATION_v0"
        ),
        "attempted_stage_count": 0,
        "authorized_stage_count": 5,
        "captured_at_utc": "2026-07-31T20:00:00Z",
        "evidence_promoted": False,
        "gravitational_action_constructed_or_selected": False,
        "gravitational_calculation_started": False,
        "installed_from_commit": installed_from_commit,
        "installed_program_state": "UNOPENED",
        "installation_authority": (
            "AUTHORIZE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_INSTALLATION"
        ),
        "manifest_hash": manifest["manifest_hash"],
        "manifest_path": MANIFEST_RELATIVE_PATH,
        "mandatory_exit_target": manifest["mandatory_exit"]["target"],
        "native_gravitational_principle_selected_or_derived": False,
        "no_subsidiary_scientific_targets": True,
        "preserved_scientific_target": (
            governance.POSITIVE_GRAVITATIONAL_PRINCIPLE_PREPARATION_TARGET
        ),
        "program_id": PROGRAM_ID,
        "repair_attempt_count": 0,
        "schema_id": (
            "toe.positive_native_gravitational_principle_derivation."
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
            "positive gravitational-principle installation artifacts already exist"
        )
    installed_from_commit = _git_head()
    manifest = build_manifest(installed_from_commit)
    governance.validate_ijson(manifest)
    MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST_PATH.write_bytes(governance._pretty_json_bytes(manifest))

    registry = governance.strict_json_load(governance.REGISTRY_PATH)
    migrated = governance.install_positive_gravitational_principle_program(
        registry
    )
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
