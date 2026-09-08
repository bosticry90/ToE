from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.artifact_custody import (
    ArtifactCustodyState,
    snapshot_artifact,
    snapshot_artifacts,
)
from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ReadOnlyValidationHygiene.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "READ_ONLY_VALIDATION_HYGIENE_20260505_v0.json"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
GUARD_PATH = REPO_ROOT / "formal" / "python" / "tools" / "tracked_output_write_guard.py"
AUTHORITY_TOOL_PATH = (
    REPO_ROOT / "formal" / "python" / "tools" / "authority_promotion_registration_report.py"
)
STATE_CORE_TOOL_PATH = (
    REPO_ROOT / "formal" / "python" / "tools" / "measure_state_core_compression_yield.py"
)
STATE_CORE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "state_core_compression_yield_report_v0.json"
)

RESULT_TOKEN = "READ_ONLY_VALIDATION_HYGIENE_ENFORCED"
CONSUMED_TARGET = "prepare_read_only_validation_hygiene_packet"
NEXT_TARGET = "review_read_only_validation_hygiene_result"
ENV_VAR = "TOE_ALLOW_TRACKED_OUTPUT_WRITES"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def test_read_only_validation_hygiene_surface_records_enforcement() -> None:
    text = _read(SURFACE_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        "read_only_validation_hygiene_v0",
        CONSUMED_TARGET,
        "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_GAP_PACKET_REVIEW",
        RESULT_TOKEN,
        NEXT_TARGET,
        ENV_VAR,
        "ReadOnlyValidationHygieneStatus",
        "read_only_validation_hygiene_consumes_target_v0",
        "read_only_validation_hygiene_consumes_selector_token_v0",
        "read_only_validation_hygiene_result_token_v0",
        "read_only_validation_hygiene_next_target_v0",
        "read_only_validation_hygiene_tracked_output_guard_added_v0",
        "read_only_validation_hygiene_env_var_required_v0",
        "read_only_validation_hygiene_authority_registration_tests_read_only_v0",
        "read_only_validation_hygiene_state_core_check_mode_default_v0",
        "read_only_validation_hygiene_pytest_mutation_forbidden_v0",
        "read_only_validation_hygiene_artifact_policy_recorded_v0",
        "read_only_validation_hygiene_authoritative_surface_index_recorded_v0",
        "read_only_validation_hygiene_axiom_count_v0",
        "read_only_validation_hygiene_qft_gr_source_map_not_authorized_v0",
        "read_only_validation_hygiene_master_action_not_promoted_v0",
        "read_only_validation_hygiene_no_pillar_completion_v0",
        "read_only_validation_hygiene_no_seam_closure_v0",
        "read_only_validation_hygiene_no_phase2_readiness_v0",
        "read_only_validation_hygiene_no_empirical_adequacy_v0",
        "read_only_validation_hygiene_no_canonical_toe_claim_v0",
        "read_only_validation_hygiene_manifest_not_enrolled_v0",
    }:
        assert token in text

    assert "import ToeFormal.Derivation.ReadOnlyValidationHygiene" in aggregate_text


def test_read_only_validation_hygiene_report_records_guard_and_posture() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == "READ_ONLY_VALIDATION_HYGIENE_20260505_v0"
    assert report["hygiene_status"] == "enforced"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["tracked_write_guard"] == {
        "module": "formal/python/tools/tracked_output_write_guard.py",
        "required_env_var": ENV_VAR,
        "required_env_value": "1",
        "scope": "tracked canonical outputs under formal/output",
        "plain_validation_writes_tracked_outputs": False,
    }
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"]["master_action_promotion_authorized"] is False


def test_guard_blocks_tracked_output_write_without_env() -> None:
    code = (
        "from pathlib import Path\n"
        "from formal.python.tools.tracked_output_write_guard import "
        "assert_tracked_output_write_allowed\n"
        "root = Path.cwd()\n"
        "path = root / 'formal' / 'output' / "
        "'state_core_compression_yield_report_v0.json'\n"
        "assert_tracked_output_write_allowed(path, repo_root=root)\n"
    )
    env = os.environ.copy()
    env.pop(ENV_VAR, None)
    completed = subprocess.run(
        [sys.executable, "-c", code],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )
    assert completed.returncode != 0
    assert "Refusing to write tracked canonical output" in completed.stderr


def test_guard_allows_untracked_temp_output_without_env(tmp_path: Path) -> None:
    from formal.python.tools.tracked_output_write_guard import (
        assert_tracked_output_write_allowed,
    )

    assert_tracked_output_write_allowed(tmp_path / "report.json", repo_root=REPO_ROOT)


def test_state_core_measurement_default_is_read_only_check() -> None:
    before = _read(STATE_CORE_REPORT_PATH)
    env = os.environ.copy()
    env.pop(ENV_VAR, None)
    completed = subprocess.run(
        [sys.executable, str(STATE_CORE_TOOL_PATH)],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )
    assert completed.returncode == 0, completed.stderr
    assert _read(STATE_CORE_REPORT_PATH) == before


def test_authority_promotion_registration_helpers_are_pure_by_default() -> None:
    before_paths = [
        REPO_ROOT / "formal" / "output" / "authority" / "authoritative_blocker_definitions.json",
        REPO_ROOT / "formal" / "output" / "authority" / "blocker_definition_lineage.json",
        REPO_ROOT / "formal" / "output" / "recompute" / "qm_seam_coherence_under_revised_blocker.json",
        REPO_ROOT / "formal" / "output" / "recompute" / "ledger_artifact_transport_under_revised_blocker.json",
        REPO_ROOT / "formal" / "output" / "recompute" / "blocker_authority_transport_surface.json",
    ]
    before = {path: _read(path) for path in before_paths}

    from formal.python.tools.authority_promotion_registration_report import (
        record_supersession_relationship,
        register_revised_definition_as_authoritative,
        trigger_recompute_surfaces,
    )

    ruling = {"ruling": {"target_row_id": "ROW-SEAM-QM-STAT-001"}}
    auth_entry = register_revised_definition_as_authoritative(ruling)
    lineage_entry = record_supersession_relationship({})
    triggers = trigger_recompute_surfaces({})

    assert auth_entry["definition_id"] == "REVISED_BLOCKER_DEFINITION_20260411_v0"
    assert lineage_entry["new_authoritative_token"] == "REVISED_BLOCKER_DEFINITION_20260411_v0"
    assert len(triggers) == 3
    assert {path: _read(path) for path in before_paths} == before


def test_authority_promotion_registration_cli_default_is_read_only() -> None:
    before_paths = [
        REPO_ROOT / "formal" / "output" / "authority" / "authoritative_blocker_definitions.json",
        REPO_ROOT / "formal" / "output" / "authority" / "blocker_definition_lineage.json",
        REPO_ROOT / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json",
        REPO_ROOT / "formal" / "output" / "recompute" / "qm_seam_coherence_under_revised_blocker.json",
        REPO_ROOT / "formal" / "output" / "recompute" / "ledger_artifact_transport_under_revised_blocker.json",
        REPO_ROOT / "formal" / "output" / "recompute" / "blocker_authority_transport_surface.json",
    ]
    before = snapshot_artifacts(before_paths, repo_root=REPO_ROOT)
    ruling_path = (
        REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "coupling_refinement_ruling_20260411_v0.json"
    )
    ruling_state = snapshot_artifact(ruling_path, repo_root=REPO_ROOT)

    env = os.environ.copy()
    env.pop(ENV_VAR, None)
    completed = subprocess.run(
        [sys.executable, str(AUTHORITY_TOOL_PATH)],
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
        env=env,
    )

    if ruling_state.state in {
        ArtifactCustodyState.ABSENT,
        ArtifactCustodyState.EXTERNAL_CUSTODY_ONLY,
    }:
        assert completed.returncode == 1
        assert "Ruling report not found" in completed.stderr
    else:
        assert completed.returncode == 0, completed.stderr
        assert "write=False" in completed.stdout
    assert snapshot_artifacts(before_paths, repo_root=REPO_ROOT) == before


def test_hygiene_tooling_tokens_are_present() -> None:
    guard_text = _read(GUARD_PATH)
    authority_tool_text = _read(AUTHORITY_TOOL_PATH)
    state_core_tool_text = _read(STATE_CORE_TOOL_PATH)

    for token in {
        ENV_VAR,
        "assert_tracked_output_write_allowed",
        "assert_tracked_output_writes_allowed",
    }:
        assert token in guard_text

    assert "write=False" in authority_tool_text
    assert "--write" in authority_tool_text
    assert "assert_tracked_output_writes_allowed" in authority_tool_text
    assert "--write" in state_core_tool_text
    assert "existing report is stale" in state_core_tool_text


def test_read_only_validation_hygiene_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_read_only_validation_hygiene_gate.py"
    )
