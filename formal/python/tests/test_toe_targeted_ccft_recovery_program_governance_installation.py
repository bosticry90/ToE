from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.bounded_program_governance import (
    ENFORCEMENT_EXTENSION_KEY,
    PROGRAMS_KEY,
    PROGRAM_MANIFEST_PATHS,
    TARGETED_CCFT_RECOVERY_PROGRAM_ID,
    _hashed_payload,
    scope_hash,
    validate_registry_extension,
)
from formal.python.tools.toe_targeted_ccft_recovery_program_governance_installation import (
    INSTALLATION_COMMIT_EXACT_PATH_SET,
    PARSER_POLICY_RELATIVE_PATH,
    SCANNER_RELATIVE_PATH,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE_ROOT = REPO_ROOT / "formal" / "docs" / "release"
REGISTRY_PATH = RELEASE_ROOT / "LOOP_CONTROL_REGISTRY_v0.json"
INSTALLATION_PATH = (
    RELEASE_ROOT
    / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_"
    "PROGRAM_GOVERNANCE_INSTALLATION_v0.json"
)


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_manifest_binds_exact_four_stage_one_pass_program() -> None:
    manifest = _read(
        REPO_ROOT / PROGRAM_MANIFEST_PATHS[TARGETED_CCFT_RECOVERY_PROGRAM_ID]
    )
    assert manifest["manifest_mode"] == "PROSPECTIVE_STATIC"
    assert manifest["authorized_stage_count"] == 4
    assert manifest["targeted_content_search_pass_limit"] == 1
    assert manifest["repair_attempt_count"] == 0
    assert manifest["no_subsidiary_scientific_targets"] is True
    assert manifest["manifest_hash"] == _hashed_payload(manifest, "manifest_hash")
    assert manifest["installation_envelope"]["commit_exact_path_set"] == sorted(
        INSTALLATION_COMMIT_EXACT_PATH_SET
    )
    assert [stage["stage_number"] for stage in manifest["stages"]] == [1, 2, 3, 4]
    assert [stage["semantic_stage_id"] for stage in manifest["stages"]] == [
        "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY",
        "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION",
        "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION",
        "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF",
    ]
    for stage in manifest["stages"]:
        assert stage["canonical_scope_hash"] == scope_hash(stage["canonical_scope"])


def test_manifest_freezes_caps_outcomes_parser_tools_and_handoff() -> None:
    manifest = _read(
        REPO_ROOT / PROGRAM_MANIFEST_PATHS[TARGETED_CCFT_RECOVERY_PROGRAM_ID]
    )
    caps = manifest["workload_caps"]
    assert caps["maximum_deep_review_files"] == 96
    assert caps["maximum_deep_review_files_per_branch"] == 48
    assert caps["maximum_total_deep_review_bytes"] == 536870912
    assert manifest["program_terminal_outcomes"] == [
        "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERED",
        "NO_ADDITIONAL_CCFT_CLOSURE_EVIDENCE_FOUND",
    ]
    assert set(manifest["result_state_mapping"].values()) == {
        "PASS",
        "BLOCKED",
        "FAILED",
    }
    parser = manifest["parser_and_tool_binding"]
    assert parser["policy_path"] == PARSER_POLICY_RELATIVE_PATH
    assert parser["scanner_path"] == SCANNER_RELATIVE_PATH
    assert len(parser["policy_sha256"]) == 64
    assert len(parser["scanner_sha256"]) == 64
    handoff = manifest["required_post_outcome_handoff"]
    assert handoff["applies_after_either_scientific_terminal_outcome"] is True
    assert handoff["preparation_authorized_by_recovery_program"] is False


def test_registry_projects_program_as_installed_unopened() -> None:
    registry = _read(REGISTRY_PATH)
    program = registry[PROGRAMS_KEY][TARGETED_CCFT_RECOVERY_PROGRAM_ID]
    assert program["state"] == "UNOPENED"
    assert program["current_stage_number"] == 0
    assert program["attempted_stage_ids"] == []
    assert program["events"] == []
    assert program["event_chain_tip_hash"] is None
    assert program["last_closed_attempt_number"] == 0
    assert program["repair_attempt_count"] == 0
    assert program["program_terminal_status"] == "INSTALLED_UNOPENED"
    assert TARGETED_CCFT_RECOVERY_PROGRAM_ID in (
        registry[ENFORCEMENT_EXTENSION_KEY]["program_manifests"]
    )
    validate_registry_extension(registry)


def test_installation_is_governance_only_and_opens_no_stage() -> None:
    installation = _read(INSTALLATION_PATH)
    assert installation["installation_authority"] == (
        "AUTHORIZE_TARGETED_CCFT_RECOVERY_PROGRAM_INSTALLATION"
    )
    assert installation["installed_program_state"] == "UNOPENED"
    assert installation["attempted_stage_count"] == 0
    assert installation["stage_1_opened"] is False
    assert installation["scientific_execution_authorized"] is False
    assert installation["scientific_output_created"] is False
    assert installation["archive_traversal_executed"] is False
    assert installation["closure_contract_recovered_or_rejected"] is False
    assert installation["ccft_equation_repaired_or_selected"] is False
    assert installation["new_ccft_postulate_inserted"] is False
    assert installation["ccft_v0_constructed"] is False
    assert installation["evidence_promoted"] is False
