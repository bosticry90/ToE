from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_source_admissibility_review_for_provisional_scalar_source_report import (
    ARTIFACT_ID,
    DEFAULT_OUT,
    GENERIC_SOURCE_ADMISSIBILITY_BOUNDARY,
    LEAN_PACKET_PATH,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LOCAL_ADMISSIBILITY_SCOPE,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
    SCHEMA_ID,
    SEMICLASSICAL_COUPLING_GATE_SCOPE,
    build_qft_gr_source_admissibility_review_for_provisional_scalar_source,
)
from formal.python.tools.qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source_report import (
    BIANCHI_COMPATIBILITY_RESULT,
    DEFAULT_OUT as BIANCHI_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
)
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    DIVERGENCE_IDENTITY,
    SCALAR_EQUATION_OF_MOTION,
    WEAK_CONSERVATION_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_source_admissibility_review_for_provisional_scalar_source_report.py"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
SCALAR_SANDBOX_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRScalarSandbox.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_source_admissibility_review_files_exist() -> None:
    for path in [
        BIANCHI_PACKET_PATH,
        DEFAULT_OUT,
        TOOL_PATH,
        LEAN_PACKET_PATH,
        LEAN_VALIDATION_POLICY_PATH,
        QFTGR_AGGREGATE_PATH,
        SCALAR_SANDBOX_AGGREGATE_PATH,
        CURRENT_TARGET_AGGREGATE_PATH,
        CURRENT_AUTHORITY_AGGREGATE_PATH,
    ]:
        assert path.exists(), path


def test_source_admissibility_review_packet_records_local_result() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["artifact_id"] == ARTIFACT_ID
    assert packet["schema_id"] == SCHEMA_ID
    assert packet["packet_id"] == PACKET_ID
    assert packet["prepared"] is True
    assert packet["accepted"] is True
    assert packet["outcome_id"] == OUTCOME_ID
    assert packet["packet_classification"] == PACKET_CLASSIFICATION
    assert packet["consumed_target"] == CONSUMED_TARGET
    assert packet["selected_next_target"] == NEXT_TARGET
    assert packet["selected_next_target_kind"] == NEXT_TARGET_KIND
    assert packet["provisional_scalar_source_admissibility_result"] == (
        PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT
    )
    assert packet["local_source_admissibility_review_completed"] is True
    assert packet["local_source_admissibility_review_passed"] is True
    assert packet["provisional_scalar_source_passes_local_source_admissibility_review"] is True
    assert packet["provisional_scalar_source_admissibility_constructed"] is True
    assert packet["provisional_scalar_source_admissibility_claimed_scope"] == (
        LOCAL_ADMISSIBILITY_SCOPE
    )
    assert packet["generic_source_admissibility_boundary"] == (
        GENERIC_SOURCE_ADMISSIBILITY_BOUNDARY
    )
    assert packet["semiclassical_coupling_gate_scope"] == SEMICLASSICAL_COUPLING_GATE_SCOPE
    assert packet["weak_conservation_result"] == WEAK_CONSERVATION_RESULT
    assert packet["bianchi_compatibility_result"] == BIANCHI_COMPATIBILITY_RESULT
    assert packet["scalar_equation_of_motion"] == SCALAR_EQUATION_OF_MOTION
    assert packet["divergence_identity"] == DIVERGENCE_IDENTITY
    assert (
        build_qft_gr_source_admissibility_review_for_provisional_scalar_source()
        == packet
    )


def test_local_review_criteria_pass_and_broader_rows_remain_unclaimed() -> None:
    packet = _json(DEFAULT_OUT)
    rows = {row["row_id"]: row for row in packet["local_review_criteria"]}
    assert list(rows) == [
        "candidate_source_object_selected",
        "test_domain_and_pairing_convention_supplied",
        "weak_pairing_constructed",
        "action_derivability_constructed",
        "field_equation_on_shell_condition_stated",
        "weak_conservation_constructed_conditionally",
        "bianchi_compatibility_constructed_conditionally",
        "scope_restrictions_preserved",
    ]
    assert packet["local_review_criteria_count"] == 8
    assert packet["local_review_criteria_passed_count"] == 8
    for row in rows.values():
        assert row["status"] == "passed_conditionally", row
    broader = {row["row_id"]: row for row in packet["broader_nonclaim_rows"]}
    assert broader["state_expectation_functional_link"]["status"] == "not_supplied"
    assert broader["renormalized_stress_energy_object_and_finiteness"]["status"] == (
        "not_supplied"
    )
    assert broader["semiclassical_einstein_equation_derivation"]["status"] == (
        "not_reached"
    )


def test_source_admissibility_review_preserves_nonclaims() -> None:
    packet = _json(DEFAULT_OUT)
    for key in [
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "arbitrary_distributional_source_admissibility_claimed",
        "arbitrary_distributional_source_conservation_claimed",
        "arbitrary_distributional_source_promoted",
        "toe_native_matter_sector_defined",
        "toe_matter_model_derived",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "quantum_stress_energy_expectation_constructed",
        "state_expectation_functional_link_claimed",
        "renormalization_result_claimed",
        "renormalized_stress_energy_constructed",
        "semiclassical_einstein_equation_derived",
        "semiclassical_coupling_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "public_submission_authorized",
        "master_action_promoted",
        "master_action_promotion_authorized",
    ]:
        assert packet[key] is False, key
    assert "SOURCE_ADMISSIBILITY_ESTABLISHED" in packet["critical_gate_fail_conditions"]
    assert "semiclassical_Einstein_equation_derivation" in packet[
        "critical_gate_fail_conditions"
    ]
    assert "quantum_stress_energy_expectation_construction" in packet[
        "critical_gate_fail_conditions"
    ]


def test_tiered_lean_policy_and_aggregate_targets_are_recorded() -> None:
    packet = _json(DEFAULT_OUT)
    policy = packet["validation_policy"]
    policy_text = _read(LEAN_VALIDATION_POLICY_PATH)
    assert policy["policy_id"] == LEAN_VALIDATION_POLICY_ID
    assert policy["tiered_lean_validation_policy_formalized"] is True
    assert [row["tier"] for row in policy["tiers"]] == [1, 2, 3, 4]
    assert policy["aggregate_timeout_with_steady_progress_interpretation"] == (
        "incomplete_validation_not_mathematical_failure"
    )
    assert policy["toeformal_import_update_requires_preservation_status"] is True
    assert policy["aggregate_lean_validation_status_for_packet"] == (
        "incomplete_due_to_timeout_with_steady_progress"
    )
    assert policy["aggregate_lean_validation_required_reason"] == (
        "ToeFormal.lean import surface updated by this packet"
    )
    assert policy["aggregate_lean_validation_command"] == (
        "./run_lean.ps1 -Target ToeFormal -TimeoutSeconds 1800"
    )
    assert policy["aggregate_lean_validation_exit_code"] == 124
    assert policy["aggregate_lean_validation_elapsed_seconds"] == 1800
    assert policy["aggregate_lean_validation_observed_progress"] == (
        "built_8166_of_8179_modules_before_timeout"
    )
    assert policy["aggregate_lean_validation_mathematical_failure_claimed"] is False
    assert policy["aggregate_lean_validation_completion_claimed"] is False
    assert policy["aggregate_lean_validation_deferred"] is False
    for target in [
        "ToeFormal.Derivation.QFTGR",
        "ToeFormal.Derivation.QFTGRScalarSandbox",
        "ToeFormal.Derivation.CurrentTarget",
        "ToeFormal.Release.CurrentAuthority",
    ]:
        assert target in packet["lane_level_lean_targets"]
        assert target in policy_text
    assert "incomplete validation" in policy_text
    assert "not mathematical failure" in policy_text


def test_source_admissibility_review_rotates_live_target_to_coupling_scope_review() -> None:
    registry = _json(REGISTRY_PATH)
    skip_if_not_current_target(registry, NEXT_TARGET)
    state = registry["current_target_state"]
    active = [row for row in registry["workstreams"] if row.get("status") == "active"]
    assert len(active) == 1
    assert state["previous_live_next_target"] == CONSUMED_TARGET
    assert state["live_next_target"] == NEXT_TARGET
    assert state["active_lane"] == NEXT_TARGET
    assert state["live_next_target_evidence"] == (
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRSourceAdmissibilityReviewForProvisionalScalarSource.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_SOURCE_ADMISSIBILITY_REVIEW_FOR_PROVISIONAL_SCALAR_SOURCE_"
        "20260617_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert state["next_strict_target_coverage"][CONSUMED_TARGET][
        "status"
    ] == "completed_consumed_live_target"
    assert state["next_strict_target_coverage"][NEXT_TARGET][
        "status"
    ] == "active_live_next_target"

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["provisional_scalar_source_admissibility_constructed"] == "yes"
    assert consumed["source_admissibility_claimed"] == "no"
    assert consumed["semiclassical_einstein_equation_derived"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["provisional_scalar_source_admissibility_constructed"] == "yes"
    assert active_row["semiclassical_coupling_gate_scope_review_authorized"] == "yes"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["semiclassical_coupling_claimed"] == "no"
    assert active_row["semiclassical_einstein_equation_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_source_admissibility_review_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
            QFTGR_AGGREGATE_PATH,
            SCALAR_SANDBOX_AGGREGATE_PATH,
            CURRENT_TARGET_AGGREGATE_PATH,
            CURRENT_AUTHORITY_AGGREGATE_PATH,
            TOE_FORMAL_PATH,
            REGISTRY_PATH,
            SURFACES_PATH,
            FRONTIER_PATH,
            README_PATH,
            STATE_PATH,
            ROADMAP_PATH,
            STRICT_MAP_PATH,
        ]
    )
    for token in [
        PACKET_ID,
        OUTCOME_ID,
        PACKET_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
        "QFTGRSourceAdmissibilityReviewForProvisionalScalarSource",
        "ToeFormal.Derivation.QFTGRScalarSandbox",
        "ToeFormal.Derivation.CurrentTarget",
        "ToeFormal.Release.CurrentAuthority",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source",
        "conditional local",
        "no generic source admissibility",
        "no semiclassical Einstein equation derivation",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_source_admissibility_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_admissibility_review_for_provisional_scalar_source_gate.py"
    )
