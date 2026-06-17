from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source_report import (
    ARTIFACT_ID,
    BIANCHI_COMPATIBILITY_RESULT,
    BIANCHI_COMPATIBILITY_STATEMENT,
    CONNECTION_SCOPE,
    CONSUMED_TARGET,
    CONTRACTED_BIANCHI_IDENTITY,
    COUPLING_CONSTANT_SCOPE,
    DEFAULT_OUT,
    EINSTEIN_SOURCE_EQUATION_FORM,
    EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM,
    LEAN_PACKET_PATH,
    METRIC_COMPATIBILITY_IDENTITY,
    NEXT_TARGET,
    NEXT_TARGET_KIND,
    OUTCOME_ID,
    PACKET_CLASSIFICATION,
    PACKET_ID,
    PROVISIONAL_SOURCE_SCOPE,
    SCHEMA_ID,
    SEMICLASSICAL_NONDERIVATION_BOUNDARY,
    SOURCE_SIDE_CONSERVATION_REQUIREMENT,
    build_qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source,
)
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    DEFAULT_OUT as WEAK_CONSERVATION_PACKET_PATH,
    DIVERGENCE_IDENTITY,
    ON_SHELL_CONSERVATION_STATEMENT,
    OUTCOME_ID as WEAK_CONSERVATION_OUTCOME,
    SCALAR_EQUATION_OF_MOTION,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
    WEAK_CONSERVATION_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source_report.py"
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


def test_bianchi_compatibility_packet_files_exist() -> None:
    assert WEAK_CONSERVATION_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_PACKET_PATH.exists()


def test_bianchi_compatibility_packet_records_test_calculation() -> None:
    prior = _json(WEAK_CONSERVATION_PACKET_PATH)
    packet = _json(DEFAULT_OUT)
    assert prior["outcome_id"] == WEAK_CONSERVATION_OUTCOME
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
    assert packet["bianchi_compatibility_result"] == BIANCHI_COMPATIBILITY_RESULT
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
    assert packet["contracted_bianchi_identity"] == CONTRACTED_BIANCHI_IDENTITY
    assert packet["metric_compatibility_identity"] == METRIC_COMPATIBILITY_IDENTITY
    assert packet["einstein_source_equation_form"] == EINSTEIN_SOURCE_EQUATION_FORM
    assert packet["einstein_source_equation_with_lambda_form"] == (
        EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM
    )
    assert packet["source_side_conservation_requirement"] == (
        SOURCE_SIDE_CONSERVATION_REQUIREMENT
    )
    assert packet["bianchi_compatibility_statement"] == BIANCHI_COMPATIBILITY_STATEMENT
    assert packet["coupling_constant_scope"] == COUPLING_CONSTANT_SCOPE
    assert packet["connection_scope"] == CONNECTION_SCOPE
    assert packet["provisional_source_scope"] == PROVISIONAL_SOURCE_SCOPE
    assert packet["semiclassical_nonderivation_boundary"] == (
        SEMICLASSICAL_NONDERIVATION_BOUNDARY
    )


def test_bianchi_compatibility_derivation_steps_are_substantive() -> None:
    packet = _json(DEFAULT_OUT)
    steps = {row["step_id"]: row for row in packet["derivation_steps"]}
    assert list(steps) == [
        "state_einstein_source_test_equation",
        "state_bianchi_identity",
        "state_metric_compatibility",
        "take_divergence_of_source_equation",
        "insert_scalar_weak_conservation",
        "conclude_on_shell_bianchi_compatibility",
    ]
    assert EINSTEIN_SOURCE_EQUATION_FORM in steps[
        "state_einstein_source_test_equation"
    ]["mathematical_content"]
    assert CONTRACTED_BIANCHI_IDENTITY in steps["state_bianchi_identity"][
        "mathematical_content"
    ]
    assert METRIC_COMPATIBILITY_IDENTITY in steps["state_metric_compatibility"][
        "mathematical_content"
    ]
    assert "8 pi G_N nabla_mu T^{mu nu}" in steps[
        "take_divergence_of_source_equation"
    ]["mathematical_content"]
    assert DIVERGENCE_IDENTITY in steps["insert_scalar_weak_conservation"][
        "mathematical_content"
    ]
    assert BIANCHI_COMPATIBILITY_STATEMENT in steps[
        "conclude_on_shell_bianchi_compatibility"
    ]["mathematical_content"]


def test_bianchi_compatibility_preserves_nonclaims_and_next_stage() -> None:
    packet = _json(DEFAULT_OUT)
    assert packet["weak_conservation_constructed"] is True
    assert packet["bianchi_compatibility_constructed"] is True
    assert packet["bianchi_compatibility_constructed_scope"] == (
        "provisional scalar source on shell under imposed Einstein-form "
        "compatibility equation only"
    )
    assert packet["Bianchi_compatibility_claimed"] is True
    assert packet["Bianchi_compatibility_claimed_scope"] == (
        "conditional on scalar EOM, Levi-Civita connection, metric "
        "compatibility, constant coupling, and provisional scalar source only"
    )
    for key in [
        "semiclassical_einstein_equation_derived",
        "semiclassical_coupling_claimed",
        "source_admissibility_claimed",
        "source_admissibility_completed",
        "arbitrary_distributional_source_admissibility_claimed",
        "arbitrary_distributional_source_conservation_claimed",
        "arbitrary_distributional_source_promoted",
        "toe_native_matter_sector_defined",
        "toe_matter_model_derived",
        "toe_native_matter_derivation_claimed",
        "standard_model_derivation_claimed",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "empirical_validation_claimed",
        "public_readiness_claimed",
        "public_submission_authorized",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    progression = {row["stage"]: row for row in packet["downstream_progression"]}
    assert progression["bianchi_compatibility"][
        "status"
    ] == "CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL"
    assert progression["bianchi_compatibility"][
        "decision"
    ] == BIANCHI_COMPATIBILITY_RESULT
    assert progression["source_admissibility"]["status"] == "NEXT_TARGET_AUTHORIZED"
    assert progression["source_admissibility"]["decision"] == NEXT_TARGET
    assert progression["semiclassical_coupling"]["status"] == "NOT_REACHED"
    assert progression["qft_gr_closure"]["status"] == "NOT_CLAIMED"
    for key, value in packet["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert (
        build_qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source()
        == packet
    )


def test_bianchi_compatibility_rotates_live_target_to_source_admissibility_review() -> None:
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
        "QFTGRBianchiCompatibilityTestForProvisionalScalarStressEnergySource.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_BIANCHI_COMPATIBILITY_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_"
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
    assert consumed["bianchi_compatibility_result"] == BIANCHI_COMPATIBILITY_RESULT
    assert consumed["bianchi_compatibility_constructed"] == "yes"
    assert consumed["Bianchi_compatibility_claimed"] == "yes"
    assert consumed["source_admissibility_claimed"] == "no"
    assert consumed["semiclassical_einstein_equation_derived"] == "no"
    assert consumed["qft_gr_closure_claimed"] == "no"
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["bianchi_compatibility_result"] == BIANCHI_COMPATIBILITY_RESULT
    assert active_row["bianchi_compatibility_constructed"] == "yes"
    assert active_row["Bianchi_compatibility_claimed"] == "yes"
    assert active_row["source_admissibility_review_authorized"] == "yes"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["arbitrary_distributional_source_admissibility_claimed"] == "no"
    assert active_row["semiclassical_einstein_equation_derived"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_bianchi_compatibility_lean_and_surface_mirrors() -> None:
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
        BIANCHI_COMPATIBILITY_RESULT,
        CONTRACTED_BIANCHI_IDENTITY,
        METRIC_COMPATIBILITY_IDENTITY,
        EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM,
        SOURCE_SIDE_CONSERVATION_REQUIREMENT,
        BIANCHI_COMPATIBILITY_STATEMENT,
        "QFTGRBianchiCompatibilityTestForProvisionalScalarStressEnergySource",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_source_admissibility_review_for_provisional_scalar_source",
        "on shell",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_bianchi_compatibility_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source_gate.py"
    )
