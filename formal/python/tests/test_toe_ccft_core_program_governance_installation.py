from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    CCFT_CORE_PROGRAM_ID,
    ENFORCEMENT_EXTENSION_KEY,
    PROGRAMS_KEY,
    PROGRAM_MANIFEST_PATHS,
    _hashed_payload,
    scope_hash,
    validate_registry_extension,
)
from formal.python.tools.toe_ccft_core_program_governance_installation import (
    INSTALLATION_COMMIT_EXACT_PATH_SET,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"
INSTALLATION_PATH = (
    RELEASE_ROOT
    / "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_"
    "PROGRAM_GOVERNANCE_INSTALLATION_v0.json"
)
REVIEW_PATH = (
    RELEASE_ROOT
    / "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_"
    "PROGRAM_GOVERNANCE_INSTALLATION_RESULT_REVIEW_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_manifest_binds_exact_prepared_five_stage_program() -> None:
    manifest = _read(REPO_ROOT / PROGRAM_MANIFEST_PATHS[CCFT_CORE_PROGRAM_ID])
    assert manifest["manifest_mode"] == "PROSPECTIVE_STATIC"
    assert manifest["authorized_stage_count"] == 5
    assert manifest["repair_attempt_count"] == 0
    assert manifest["no_subsidiary_scientific_targets"] is True
    assert manifest["manifest_hash"] == _hashed_payload(manifest, "manifest_hash")
    assert manifest["installation_envelope"]["commit_exact_path_set"] == sorted(
        INSTALLATION_COMMIT_EXACT_PATH_SET
    )
    assert [stage["stage_number"] for stage in manifest["stages"]] == [1, 2, 3, 4, 5]
    assert [stage["semantic_stage_id"] for stage in manifest["stages"]] == [
        "CCFT_SOURCE_BOUND_MATHEMATICAL_INVENTORY",
        "CCFT_MATHEMATICAL_LINEAGE_AND_CONFLICT_RECONCILIATION",
        "CCFT_MATHEMATICAL_OBJECT_OPERATIONALIZATION",
        "MINIMAL_CLOSED_CCFT_CORE_DECISION",
        "CCFT_VIABILITY_TEST_HANDOFF_DECISION",
    ]
    for stage in manifest["stages"]:
        assert stage["canonical_scope_hash"] == scope_hash(stage["canonical_scope"])
        assert stage["mandatory_terminal_outcomes"] == (
            stage["canonical_scope"]["terminal_outcome_vocabulary"]
        )


def test_manifest_freezes_caps_scope_and_result_states() -> None:
    manifest = _read(REPO_ROOT / PROGRAM_MANIFEST_PATHS[CCFT_CORE_PROGRAM_ID])
    assert manifest["workload_caps"]["maximum_source_artifacts_for_deep_review"] == 160
    assert manifest["workload_caps"]["maximum_total_deep_review_source_bytes"] == 536870912
    assert manifest["workload_caps"]["maximum_minimal_core_candidates"] == 12
    assert manifest["source_scope_contract"]["repository_claim_exhaustion_may_be_claimed"] is False
    assert manifest["passive_content_contract"]["archived_code_import_execution_or_compilation"] is False
    assert set(manifest["result_state_mapping"].values()) == {
        "PASS",
        "BLOCKED",
        "FAILED",
    }


def test_registry_projects_program_as_installed_unopened() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][CCFT_CORE_PROGRAM_ID]
    assert program["state"] == "UNOPENED"
    assert program["current_stage_number"] == 0
    assert program["attempted_stage_ids"] == []
    assert program["events"] == []
    assert program["event_chain_tip_hash"] is None
    assert program["last_closed_attempt_number"] == 0
    assert program["repair_attempt_count"] == 0
    assert program["program_terminal_status"] == "INSTALLED_UNOPENED"
    assert registry["current_projection_v0"]["current_target"] == (
        "prepare_toe_ccft_native_mathematical_core_and_operationalization_"
        "bounded_program_v0"
    )
    assert CCFT_CORE_PROGRAM_ID in (
        registry[ENFORCEMENT_EXTENSION_KEY]["program_manifests"]
    )
    validate_registry_extension(registry)


def test_installation_is_governance_only_and_opens_no_stage() -> None:
    installation = _read(INSTALLATION_PATH)
    assert installation["installation_authority"] == (
        "AUTHORIZE_CCFT_CORE_PROGRAM_INSTALLATION"
    )
    assert installation["status"] == (
        "PROGRAM_GOVERNANCE_INSTALLED_UNOPENED_NO_SCIENTIFIC_ROTATION"
    )
    assert installation["installed_program_state"] == "UNOPENED"
    assert installation["attempted_stage_count"] == 0
    assert installation["stage_1_opened"] is False
    assert installation["scientific_execution_authorized"] is False
    assert installation["scientific_output_created"] is False
    assert installation["ccft_model_or_physical_claim_established"] is False
    assert installation["ccft_mathematical_core_recovered"] is False
    assert installation["operational_coherence_definition_established"] is False
    assert installation["ccft_representation_or_field_selected"] is False
    assert installation["ccft_action_or_evolution_law_constructed"] is False
    assert installation["ccft_seam_observable_or_discriminator_selected"] is False
    assert installation["evidence_promoted"] is False


def test_installation_commit_has_exact_envelope_and_parent() -> None:
    installation = _read(INSTALLATION_PATH)
    commit = "6b9b9b16418d5e709870d4079918abad53b8526a"
    names = subprocess.run(
        ["git", "show", "--format=", "--name-only", commit],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    assert sorted(path for path in names if path) == sorted(
        INSTALLATION_COMMIT_EXACT_PATH_SET
    )
    parent = subprocess.run(
        ["git", "rev-parse", f"{commit}^"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    assert parent == installation["installed_from_commit"]


def test_independent_review_accepts_only_the_unopened_installation() -> None:
    review = _read(REVIEW_PATH)
    assert review["accepted"] is True
    assert review["status"] == (
        "INSTALLATION_ACCEPTED_PROGRAM_UNOPENED_NO_SCIENTIFIC_RESULT"
    )
    assert review["program_state"] == "UNOPENED"
    assert review["attempted_stage_count"] == 0
    assert review["stage_1_opened"] is False
    assert review["scientific_execution_authorized"] is False
    assert review["scientific_output_created"] is False
    assert review["ccft_model_or_physical_claim_established"] is False
    assert review["ccft_mathematical_core_recovered"] is False
    assert review["operational_coherence_definition_established"] is False
    assert review["ccft_representation_or_field_selected"] is False
    assert review["ccft_action_or_evolution_law_constructed"] is False
    assert review["ccft_seam_observable_or_discriminator_selected"] is False
    assert review["evidence_promoted"] is False
    assert review["exhaustive_python_passage_established"] is False
    assert all(review["checks"].values())
