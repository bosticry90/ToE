from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
    skip_if_not_current_target,
)
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_report import (
    CONTRACT_RESULT,
    DEFAULT_OUT as FUNCTIONAL_CONTRACT_PACKET_PATH,
    OUTCOME_ID as FUNCTIONAL_CONTRACT_PACKET_OUTCOME,
)
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review_report import (
    ARTIFACT_ID,
    CANDIDATE_SOURCE_ID,
    CONSUMED_TARGET,
    DEFAULT_OUT,
    LEAN_REVIEW_PATH,
    NEXT_TARGET,
    OUTCOME_ID,
    PAIRING_FORMULA,
    REQUIRED_FUNCTIONAL_CONTRACT,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEWED_COMMIT,
    REVIEWED_LIVE_TARGET_BEFORE_REVIEW,
    REVIEW_ID,
    SCHEMA_ID,
    TEST_SPACE,
    build_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review_report.py"
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


def test_candidate_functional_contract_packet_result_review_files_exist() -> None:
    assert FUNCTIONAL_CONTRACT_PACKET_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_REVIEW_PATH.exists()


def test_candidate_functional_contract_packet_result_review_accepts_blocked_result() -> None:
    review = _json(DEFAULT_OUT)
    packet = _json(FUNCTIONAL_CONTRACT_PACKET_PATH)
    assert packet["outcome_id"] == FUNCTIONAL_CONTRACT_PACKET_OUTCOME
    assert packet["contract_result"] == CONTRACT_RESULT
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
    assert review["contract_result"] == CONTRACT_RESULT
    assert review["contract_result_accepted"] is True


def test_review_confirms_contract_material_and_missing_type_domain_data() -> None:
    review = _json(DEFAULT_OUT)
    assert review["test_space"] == TEST_SPACE
    assert review["required_functional_contract"] == REQUIRED_FUNCTIONAL_CONTRACT
    assert review["smooth_or_locally_integrable_pairing_formula"] == PAIRING_FORMULA
    assert review["candidate_functional_contract_constructed"] is False
    assert review["candidate_functional_contract_rejected"] is False
    assert review["contract_option_selected"] is False
    assert review["multiple_candidate_functional_contract_options_recorded"] is True
    assert review["missing_regular_type_and_domain_data_confirmed"] is True
    assert review["next_packet_required_question"].startswith(
        "What mathematical regular type and domain contract"
    )
    assert review["regular_type_options_to_assess"] == [
        "smooth_symmetric_tensor_field",
        "locally_integrable_tensor_field",
        "tensor_valued_distribution",
        "tensor_density",
        "operator_valued_distribution_expectation_candidate",
        "undefined_or_insufficiently_specified",
    ]


def test_review_preserves_nonclaims_and_downstream_blocking() -> None:
    review = _json(DEFAULT_OUT)
    assert review["weak_pairing_retry_authorized"] is False
    assert review["weak_pairing_completed"] is False
    assert review["well_defined_pairing"] == "not_reached"
    assert review["action_derivability_status"] == "not_reached"
    assert review["weak_conservation_status"] == "not_reached"
    assert review["bianchi_compatibility_status"] == "not_reached"
    assert review["semiclassical_source_admissibility_status"] == "not_reached"
    for key in [
        "source_admissibility_claimed",
        "action_derivability_claimed",
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
        build_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review()
        == review
    )


def test_review_updates_live_target_to_regular_type_domain_packet() -> None:
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
        "QFTGRBroaderStressEnergyLikeDistributionCandidateFunctionalContractPacketResultReview.lean"
    )
    assert state["live_next_target_report"] == (
        "formal/docs/release/"
        "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_"
        "FUNCTIONAL_CONTRACT_PACKET_RESULT_REVIEW_20260616_v0.json"
    )
    assert state["live_next_target_outcome"] == OUTCOME_ID
    assert CONSUMED_TARGET in registry["completed_targets"]
    assert CONSUMED_TARGET in registry["next_strict_target_coverage"]
    assert NEXT_TARGET in registry["next_strict_target_coverage"]

    consumed = _workstream(registry, CONSUMED_TARGET)
    assert consumed["status"] == "paused"
    assert consumed["result_review_accepted"] == "yes"
    assert consumed["reviewed_artifact_id"] == (
        "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_"
        "FUNCTIONAL_CONTRACT_PACKET_20260616_v0"
    )
    assert consumed["reviewed_commit"] == REVIEWED_COMMIT
    assert consumed["selected_next_target"] == NEXT_TARGET

    active_row = active[0]
    assert active_row["workstream_id"] == NEXT_TARGET
    assert active_row["authorized_next_strict_target"] == NEXT_TARGET
    assert active_row["consumed_target"] == CONSUMED_TARGET
    assert active_row["contract_result"] == CONTRACT_RESULT
    assert active_row["candidate_source_id"] == CANDIDATE_SOURCE_ID
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
        CONTRACT_RESULT,
        REQUIRED_FUNCTIONAL_CONTRACT,
        "smooth_symmetric_tensor_field",
        "operator_valued_distribution_expectation_candidate",
        "QFTGRBroaderStressEnergyLikeDistributionCandidateFunctionalContractPacketResultReview",
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "prepare_qft_gr_broader_stress_energy_like_distribution_candidate_regular_"
        "type_and_domain_contract_packet",
        "no weak-pairing retry",
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_candidate_functional_contract_packet_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review_gate.py"
    )
