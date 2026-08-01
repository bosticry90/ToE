"""Install the bounded targeted CCFT closure-evidence recovery program unopened."""

from __future__ import annotations

import hashlib
import subprocess
from typing import Any

from formal.python.tools import bounded_program_governance as governance
from formal.python.tools.loop_control_registry_integrity import atomic_write_registry


REPO_ROOT = governance.REPO_ROOT
PROGRAM_ID = governance.TARGETED_CCFT_RECOVERY_PROGRAM_ID
MANIFEST_RELATIVE_PATH = governance.PROGRAM_MANIFEST_PATHS[PROGRAM_ID]
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
PREPARATION_RESULT_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_"
    "PREPARATION_RESULT_v0.json"
)
PREPARATION_RESULT_PATH = REPO_ROOT / PREPARATION_RESULT_RELATIVE_PATH
PREPARATION_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_"
    "PREPARATION_RESULT_REVIEW_v0.json"
)
INSTALLATION_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_"
    "PROGRAM_GOVERNANCE_INSTALLATION_v0.json"
)
INSTALLATION_PATH = REPO_ROOT / INSTALLATION_RELATIVE_PATH
PARSER_POLICY_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_"
    "PREINSTALLATION_CONTROLS_20260730_v0.json"
)
SCANNER_RELATIVE_PATH = (
    "formal/python/tools/native_hypothesis_census_index_v1.py"
)

INSTALLATION_COMMIT_EXACT_PATH_SET = [
    "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
    INSTALLATION_RELATIVE_PATH,
    MANIFEST_RELATIVE_PATH,
    "formal/python/tests/"
    "test_toe_targeted_ccft_recovery_program_governance_installation.py",
    "formal/python/tools/bounded_program_governance.py",
    "formal/python/tools/"
    "toe_targeted_ccft_recovery_program_governance_installation.py",
    "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean",
    "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean",
    "formal/toe_formal/ToeFormal/Release/"
    "ToeTargetedCCFTRecoveryProgramGovernanceInstallationV0.lean",
    "formal/toe_formal/ToeFormalAll.lean",
]

COMMON_AUTHORIZED_INPUTS = [
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_SOURCE_CENSUS_RESULT_v0",
    "REPOSITORY_WIDE_SOURCE_CENSUS_AGGREGATE_MANIFEST_v1",
    "TOE_CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY_RESULT_v0",
    "TOE_CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION_RESULT_v0",
    "TOE_MINIMAL_CLOSED_CCFT_CORE_DECISION_RESULT_v0",
]

COMMON_PROHIBITED_CLAIMS = [
    "CCFT model closure validation or empirical confirmation",
    "equation repair completion or harmonization",
    "parameter coefficient data or boundary-condition inference",
    "new CCFT postulate insertion",
    "CP-NLSE LCRD-v3 or CCFT-v0 core selection",
    "matter gravity scale seam action or observable construction",
    "canonical evidence promotion",
    "automatic second search repair or successor authorization",
    "repository claim exhaustion",
]

STAGE_METADATA = [
    {
        "semantic_stage_id": "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY",
        "target": "discover_toe_targeted_ccft_closure_evidence_sources_v0",
        "question": (
            "Which files pass the frozen targeted CCFT branch-and-contract gate "
            "within stable custody snapshots and the fixed source budget?"
        ),
        "stem": "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY",
        "tool": "toe_targeted_ccft_closure_source_discovery_stage_authorization.py",
        "lean_open": "ToeTargetedCCFTClosureSourceDiscoveryAttemptOpen",
        "lean_result": "ToeTargetedCCFTClosureSourceDiscoveryResult",
    },
    {
        "semantic_stage_id": "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION",
        "target": "extract_toe_targeted_ccft_closure_contracts_v0",
        "question": (
            "What explicit source-bound evidence addresses the frozen CP-NLSE "
            "and LCRD-v3 missing-contract checklists?"
        ),
        "stem": "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION",
        "tool": "toe_targeted_ccft_closure_contract_extraction_stage_authorization.py",
        "lean_open": "ToeTargetedCCFTClosureContractExtractionAttemptOpen",
        "lean_result": "ToeTargetedCCFTClosureContractExtractionResult",
    },
    {
        "semantic_stage_id": "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION",
        "target": "adjudicate_toe_targeted_ccft_contract_completeness_and_conflicts_v0",
        "question": (
            "Does any extracted record explicitly, materially, and conflict-"
            "freely close a previously missing CCFT contract?"
        ),
        "stem": "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION",
        "tool": "toe_targeted_ccft_contract_adjudication_stage_authorization.py",
        "lean_open": "ToeTargetedCCFTContractAdjudicationAttemptOpen",
        "lean_result": "ToeTargetedCCFTContractAdjudicationResult",
    },
    {
        "semantic_stage_id": "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF",
        "target": "select_toe_post_targeted_ccft_recovery_construction_handoff_v0",
        "question": (
            "Which one of the two frozen recovery outcomes holds, and what "
            "separately authorized CCFT-v0 construction preparation follows?"
        ),
        "stem": "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF",
        "tool": "toe_targeted_ccft_recovery_handoff_stage_authorization.py",
        "lean_open": "ToeTargetedCCFTRecoveryHandoffAttemptOpen",
        "lean_result": "ToeTargetedCCFTRecoveryHandoffResult",
    },
]


def _sha256(relative_path: str) -> str:
    return hashlib.sha256((REPO_ROOT / relative_path).read_bytes()).hexdigest()


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
                "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_RESULT_v0",
                "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0",
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
        result_path,
        review_path,
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
            "open_commit_exact_path_set": sorted(open_paths),
            "close_commit_exact_path_set": sorted(close_paths),
            "open_event_path": open_event,
            "close_event_path": close_event,
            "result_artifact_path": result_path,
            "review_artifact_path": review_path,
        },
        "semantic_stage_id": row["semantic_stage_id"],
        "stage_number": attempt,
    }


def build_manifest(installed_from_commit: str) -> dict[str, Any]:
    prepared = governance.strict_json_load(PREPARATION_RESULT_PATH)
    prepared_stages = prepared["stages"]
    if [stage["semantic_stage_id"] for stage in prepared_stages] != [
        row["semantic_stage_id"] for row in STAGE_METADATA
    ]:
        raise governance.BoundedProgramError(
            "prepared stages do not match targeted CCFT installation metadata"
        )
    controls = prepared["program_controls"]
    workload_caps = {
        key: value for key, value in controls.items() if key.startswith("maximum_")
    }
    manifest: dict[str, Any] = {
        "authorized_stage_count": 4,
        "authorized_source_roots": prepared["authorized_source_roots_proposed"],
        "deterministic_search_contract": prepared["deterministic_search_contract"],
        "duplicate_and_lineage_contract": prepared["duplicate_and_lineage_contract"],
        "evidence_strength_vocabulary": prepared["evidence_strength_vocabulary"],
        "installation_envelope": {
            "commit_exact_path_set": sorted(INSTALLATION_COMMIT_EXACT_PATH_SET),
            "installed_from_commit": installed_from_commit,
        },
        "mandatory_exit": {
            "target": prepared["mandatory_exit_target_proposed"],
            "terminal_outcomes": prepared["program_scientific_terminal_outcomes"],
        },
        "manifest_hash": "",
        "manifest_mode": "PROSPECTIVE_STATIC",
        "missing_contract_checklists": prepared["missing_contract_checklists"],
        "native_hypothesis_tested": "HYP_TOE_CCFT_TARGETED_CLOSURE_EVIDENCE_RECOVERY_v0",
        "native_relevance": {
            "kind": "DIRECT_NATIVE_TEST",
            "statement": (
                "Tests one final bounded source-recovery pass for explicit CP-NLSE "
                "or LCRD-v3 closure contracts without repairing or constructing CCFT."
            ),
        },
        "no_subsidiary_scientific_targets": True,
        "parser_and_tool_binding": {
            "contract_version": "v1",
            "parser_classes": prepared[
                "passive_parser_and_hostile_content_contract"
            ]["parser_classes"],
            "policy_path": PARSER_POLICY_RELATIVE_PATH,
            "policy_sha256": _sha256(PARSER_POLICY_RELATIVE_PATH),
            "scanner_path": SCANNER_RELATIVE_PATH,
            "scanner_sha256": _sha256(SCANNER_RELATIVE_PATH),
        },
        "passive_content_contract": prepared[
            "passive_parser_and_hostile_content_contract"
        ],
        "positive_recovery_admissibility_rule": prepared[
            "positive_recovery_admissibility_rule"
        ],
        "program_id": PROGRAM_ID,
        "program_terminal_outcomes": prepared["program_scientific_terminal_outcomes"],
        "repair_attempt_count": 0,
        "required_post_outcome_handoff": prepared["required_post_outcome_handoff"],
        "result_state_mapping": prepared[
            "program_terminal_outcome_lifecycle_mapping"
        ],
        "root_snapshot_contract": prepared["root_snapshot_contract"],
        "schema_id": "toe.bounded_program.immutable_manifest.v1",
        "stages": [
            _stage_manifest(metadata, prepared_stage)
            for metadata, prepared_stage in zip(
                STAGE_METADATA, prepared_stages, strict=True
            )
        ],
        "status": "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST",
        "targeted_content_search_pass_limit": 1,
        "workload_caps": workload_caps,
    }
    manifest["manifest_hash"] = governance._hashed_payload(manifest, "manifest_hash")
    return manifest


def build_installation(
    *, installed_from_commit: str, manifest: dict[str, Any]
) -> dict[str, Any]:
    return {
        "artifact_id": (
            "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_"
            "PROGRAM_GOVERNANCE_INSTALLATION_v0"
        ),
        "archive_traversal_executed": False,
        "attempted_stage_count": 0,
        "authorized_stage_count": 4,
        "captured_at_utc": "2026-08-01T03:35:00Z",
        "ccft_equation_repaired_or_selected": False,
        "ccft_v0_constructed": False,
        "closure_contract_recovered_or_rejected": False,
        "evidence_promoted": False,
        "installed_from_commit": installed_from_commit,
        "installed_program_state": "UNOPENED",
        "installation_authority": (
            "AUTHORIZE_TARGETED_CCFT_RECOVERY_PROGRAM_INSTALLATION"
        ),
        "manifest_hash": manifest["manifest_hash"],
        "manifest_path": MANIFEST_RELATIVE_PATH,
        "mandatory_exit_target": manifest["mandatory_exit"]["target"],
        "new_ccft_postulate_inserted": False,
        "no_subsidiary_scientific_targets": True,
        "preserved_scientific_target": (
            governance.TARGETED_CCFT_RECOVERY_PREPARATION_TARGET
        ),
        "program_id": PROGRAM_ID,
        "repair_attempt_count": 0,
        "schema_id": (
            "toe.targeted_ccft_closure_evidence_recovery."
            "program_governance_installation.v0"
        ),
        "scientific_execution_authorized": False,
        "scientific_output_created": False,
        "stage_1_opened": False,
        "status": "PROGRAM_GOVERNANCE_INSTALLED_UNOPENED_NO_SCIENTIFIC_ROTATION",
        "targeted_content_search_pass_limit": 1,
    }


def main() -> int:
    if MANIFEST_PATH.exists() or INSTALLATION_PATH.exists():
        raise governance.BoundedProgramError(
            "targeted CCFT recovery installation artifacts already exist"
        )
    installed_from_commit = _git_head()
    manifest = build_manifest(installed_from_commit)
    governance.validate_ijson(manifest)
    MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST_PATH.write_bytes(governance._pretty_json_bytes(manifest))

    registry = governance.strict_json_load(governance.REGISTRY_PATH)
    migrated = governance.install_targeted_ccft_recovery_program(registry)
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
