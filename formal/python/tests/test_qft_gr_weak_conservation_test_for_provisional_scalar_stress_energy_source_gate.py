from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_action_derivability_retry_with_provisional_matter_sector_report import (
    ACTION_DERIVABILITY_RESULT,
    DEFAULT_OUT as ACTION_DERIVABILITY_PACKET_PATH,
    OUTCOME_ID as ACTION_DERIVABILITY_OUTCOME,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
)
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    ARTIFACT_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OFF_SHELL_BOUNDARY,
    ON_SHELL_CONSERVATION_STATEMENT,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    REGULARITY_SCOPE,
    SCALAR_EQUATION_OF_MOTION,
    SCHEMA_ID,
    WEAK_CONSERVATION_RESULT,
    WEAK_TEST_PAIRING_SCOPE,
    build_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report.py"
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


def test_weak_conservation_packet_files_exist() -> None:
    assert ACTION_DERIVABILITY_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_weak_conservation_packet_records_on_shell_calculation() -> None:
    prior = _json(ACTION_DERIVABILITY_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == ACTION_DERIVABILITY_OUTCOME
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
    assert packet["weak_conservation_result"] == WEAK_CONSERVATION_RESULT
    assert packet["action_derivability_result"] == ACTION_DERIVABILITY_RESULT
    assert packet["selected_provisional_matter_sector_id"] == (
        SELECTED_PROVISIONAL_MATTER_SECTOR_ID
    )
    assert packet["selected_action_generated_source_subclass_id"] == (
        SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
    )
    assert packet["field_content"] == SELECTED_FIELD_CONTENT
    assert packet["stress_energy_covariant_expression"] == (
        STRESS_ENERGY_COVARIANT_EXPRESSION
    )
    assert packet["scalar_equation_of_motion"] == SCALAR_EQUATION_OF_MOTION
    assert packet["divergence_identity"] == DIVERGENCE_IDENTITY
    assert packet["on_shell_conservation_statement"] == (
        ON_SHELL_CONSERVATION_STATEMENT
    )
    assert packet["off_shell_boundary"] == OFF_SHELL_BOUNDARY
    assert packet["regularity_scope"] == REGULARITY_SCOPE
    assert packet["weak_test_pairing_scope"] == WEAK_TEST_PAIRING_SCOPE


def test_weak_conservation_derivation_steps_are_substantive() -> None:
    packet = _json(DEFAULT_OUT)
    steps = {row["step_id"]: row for row in packet["derivation_steps"]}
    assert list(steps) == [
        "restate_scalar_stress_energy",
        "state_scalar_equation_of_motion",
        "compute_divergence",
        "cancel_symmetric_second_derivative_terms",
        "reduce_to_field_equation_residual",
        "conclude_on_shell_weak_conservation",
    ]
    assert STRESS_ENERGY_COVARIANT_EXPRESSION in steps[
        "restate_scalar_stress_energy"
    ]["mathematical_content"]
    assert SCALAR_EQUATION_OF_MOTION in steps["state_scalar_equation_of_motion"][
        "mathematical_content"
    ]
    assert "nabla_mu T^{mu nu}" in steps["compute_divergence"][
        "mathematical_content"
    ]
    assert "scalar phi" in steps["cancel_symmetric_second_derivative_terms"][
        "mathematical_content"
    ]
    assert DIVERGENCE_IDENTITY in steps["reduce_to_field_equation_residual"][
        "mathematical_content"
    ]
    assert ON_SHELL_CONSERVATION_STATEMENT in steps[
        "conclude_on_shell_weak_conservation"
    ]["mathematical_content"]


def test_weak_conservation_preserves_nonclaims_and_next_stage() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["action_derivability_constructed"] is True
    assert packet["weak_conservation_constructed"] is True
    assert packet["weak_conservation_constructed_scope"] == (
        "provisional real-scalar source on shell only"
    )
    assert packet["weak_conservation_claimed"] is True
    assert packet["weak_conservation_claimed_scope"] == (
        "conditional on scalar equation of motion only"
    )
    assert packet["on_shell_required"] is True
    for key in [
        "off_shell_conservation_claimed",
        "arbitrary_phi_conserved_claimed",
        "conservation_claimed",
        "unconditional_conservation_claimed",
        "toe_native_matter_sector_defined",
        "toe_matter_model_derived",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "arbitrary_distributional_source_action_derived_claimed",
        "arbitrary_distributional_source_conservation_claimed",
        "arbitrary_distributional_source_promoted",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "Bianchi_compatibility_claimed",
        "Bianchi_compatibility_completed",
        "semiclassical_coupling_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "empirical_validation_claimed",
        "public_submission_authorized",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    progression = {row["stage"]: row for row in packet["downstream_progression"]}
    assert progression["weak_conservation"][
        "status"
    ] == "CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL"
    assert progression["weak_conservation"]["decision"] == WEAK_CONSERVATION_RESULT
    assert progression["off_shell_conservation"]["status"] == "NOT_CLAIMED"
    assert progression["source_admissibility"]["status"] == "NOT_REACHED"
    assert progression["bianchi_compatibility"]["status"] == "NEXT_TARGET_AUTHORIZED"
    assert progression["bianchi_compatibility"]["decision"] == NEXT_TARGET
    assert progression["semiclassical_coupling"]["status"] == "NOT_REACHED"
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert (
        build_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source()
        == packet
    )


def test_weak_conservation_rotates_live_target_to_bianchi_test() -> None:
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
        "QFTGRWeakConservationTestForProvisionalScalarStressEnergySource.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_WEAK_CONSERVATION_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_"
        "SOURCE_20260617_v0.json"
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
    assert consumed["weak_conservation_result"] == WEAK_CONSERVATION_RESULT
    assert consumed["weak_conservation_constructed"] == "yes"
    assert consumed["weak_conservation_constructed_scope"] == (
        "provisional real-scalar source on shell only"
    )
    assert consumed["on_shell_required"] == "yes"
    assert consumed["off_shell_conservation_claimed"] == "no"
    assert consumed["arbitrary_phi_conserved_claimed"] == "no"
    assert consumed["source_admissibility_claimed"] == "no"
    assert consumed["Bianchi_compatibility_claimed"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["weak_conservation_result"] == WEAK_CONSERVATION_RESULT
    assert active_row["weak_conservation_constructed"] == "yes"
    assert active_row["weak_conservation_claimed"] == "yes"
    assert active_row["weak_conservation_claimed_scope"] == (
        "conditional on scalar equation of motion only"
    )
    assert active_row["on_shell_required"] == "yes"
    assert active_row["divergence_identity"] == DIVERGENCE_IDENTITY
    assert active_row["on_shell_conservation_statement"] == (
        ON_SHELL_CONSERVATION_STATEMENT
    )
    assert active_row["Bianchi_compatibility_test_authorized"] == "yes"
    assert active_row["Bianchi_compatibility_claimed"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["semiclassical_einstein_equation_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_weak_conservation_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_PACKET_PATH,
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
        WEAK_CONSERVATION_RESULT,
        SCALAR_EQUATION_OF_MOTION,
        DIVERGENCE_IDENTITY,
        ON_SHELL_CONSERVATION_STATEMENT,
        SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
        STRESS_ENERGY_COVARIANT_EXPRESSION,
        "QFTGRWeakConservationTestForProvisionalScalarStressEnergySource",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source",
        "on shell",
        "no source admissibility",
        "no Bianchi compatibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_weak_conservation_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_gate.py"
    )
