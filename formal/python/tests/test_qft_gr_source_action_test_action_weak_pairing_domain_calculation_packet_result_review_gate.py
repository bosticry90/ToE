from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_report import (
    CALCULATION_RESULT,
    DEFAULT_OUT as CALCULATION_PACKET_PATH,
    OUTCOME_ID as CALCULATION_PACKET_OUTCOME,
)
from formal.python.tools.qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review_report import (
    ARTIFACT_ID,
    CANDIDATE_SOURCE_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LEAN_REVIEW_PATH,
    NEXT_TARGET,
    OUTCOME_ID,
    REVIEWED_COMMIT,
    REVIEWED_LIVE_TARGET_BEFORE_REVIEW,
    REQUIRED_FUNCTIONAL_CONTRACT,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
    SCHEMA_ID,
    build_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review_report.py"
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


def test_calculation_packet_result_review_files_exist() -> None:
    assert CALCULATION_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_calculation_packet_result_review_accepts_missing_contract_blocker() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(CALCULATION_PACKET_PATH)
    assert packet["outcome_id"] == CALCULATION_PACKET_OUTCOME
    assert packet["calculation_result"] == CALCULATION_RESULT
    assert review["artifact_id"] == ARTIFACT_ID
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["reviewed_artifact_id"] == packet["schema_id"]
    assert review["reviewed_commit"] == REVIEWED_COMMIT
    assert review["reviewed_live_target_before_review"] == (
        REVIEWED_LIVE_TARGET_BEFORE_REVIEW
    )
    assert review["accepted"] is True
    assert review["result_review_accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["consumed_target"] == CONSUMED_TARGET
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["candidate_source_id"] == CANDIDATE_SOURCE_ID
    assert review["calculation_result"] == CALCULATION_RESULT
    assert review["calculation_result_accepted"] is True
    assert review["weak_pairing_attempted"] is True
    assert review["weak_pairing_decision"] == "blocked"
    assert review["weak_pairing_not_false_due_to_underspecification"] is True
    assert review["missing_candidate_functional_contract_confirmed"] is True
    assert review["required_functional_contract"] == REQUIRED_FUNCTIONAL_CONTRACT


def test_review_requires_contract_obligation_and_downstream_not_reached() -> None:
    review = _json(DEFAULT_OUT)
    obligations = review["contract_packet_required_obligations"]
    assert review["contract_packet_required_obligation_count"] == 11
    for item in [
        "background_spacetime_assumptions",
        "test_space_topology",
        "regularity_class_of_T",
        "tensor_vs_tensor_density_status",
        "index_placement",
        "metric_dependence",
        "support_and_locality_assumptions",
        "linearity",
        "continuity",
        "coordinate_or_covariance_behavior",
        "action_derived_or_merely_source_like_status",
    ]:
        assert item in obligations
    assert review["action_derivability_status"] == "not_reached"
    assert review["weak_conservation_status"] == "not_reached"
    assert review["bianchi_compatibility_status"] == "not_reached"
    assert review["semiclassical_source_admissibility_status"] == "not_reached"
    assert review["downstream_status_when_weak_pairing_blocked"] == "NOT_REACHED"


def test_review_preserves_nonclaims_and_determinism() -> None:
    review = _json(DEFAULT_OUT)
    for key in [
        "source_admissibility_claimed",
        "conservation_claimed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "empirical_validation_claimed",
        "public_submission_authorized",
        "master_action_promoted",
    ]:
        assert review[key] is False, key
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"
    assert (
        build_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review()
        == review
    )


def test_review_updates_live_target_to_functional_contract_packet() -> None:
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
        "QFTGRSourceActionTestActionWeakPairingDomainCalculationPacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_"
        "PACKET_RESULT_REVIEW_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["result_review_accepted"] == "yes"
    assert consumed["reviewed_artifact_id"] == SCHEMA_ID.replace(
        "_RESULT_REVIEW_20260616_v0", "_20260616_v0"
    )
    assert consumed["reviewed_commit"] == REVIEWED_COMMIT
    assert consumed["reviewed_live_target_before_review"] == CONSUMED_TARGET
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["calculation_result"] == CALCULATION_RESULT
    assert active_row["required_functional_contract"] == REQUIRED_FUNCTIONAL_CONTRACT
    assert active_row["weak_pairing_retry_authorized"] == "no"
    assert active_row["source_admissibility_claimed"] == "no"
    assert active_row["qft_gr_closure_claimed"] == "no"


def test_review_lean_and_surface_mirrors() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            DEFAULT_OUT,
            LEAN_REVIEW_PATH,
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
        REVIEW_ID,
        OUTCOME_ID,
        RESULT_REVIEW_CLASSIFICATION,
        CONSUMED_TARGET,
        NEXT_TARGET,
        CANDIDATE_SOURCE_ID,
        CALCULATION_RESULT,
        REQUIRED_FUNCTIONAL_CONTRACT,
        "QFTGRSourceActionTestActionWeakPairingDomainCalculationPacketResultReview",
        "prepare_qft_gr_broader_stress_energy_like_distribution_candidate_"
        "functional_contract_packet",
        "no source admissibility",
        "no QFT-GR closure",
        "no public submission",
    ]:
        assert token in joined


def test_calculation_packet_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review_gate.py"
    )
