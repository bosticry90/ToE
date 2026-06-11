from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)
from formal.python.tools.qft_gr_post_mr_assump004_governed_maturation_reports import (
    ACCEPTED_MR_ROWS,
    CLAIM_LADDER_PATH,
    CORE_HYPOTHESIS_PATH,
    COUNTERMODEL_REGISTRY_PATH,
    EXPERT_TRANSLATION_PATH,
    FALSIFIER_ADDENDUM_PATH,
    FINAL_LIVE_TARGET,
    INVENTORY_SELECTION_PATH,
    MATURATION_INDEX_PATH,
    MINIMAL_MODEL_PATH,
    MR_CLOSEOUT_PACKET_PATH,
    MR_CLOSEOUT_REVIEW_PATH,
    POST_MR_WITNESS_PACKET_TARGET,
    WITNESS_ATTEMPT_PATH,
    WITNESS_ATTEMPT_REVIEW_PATH,
    WITNESS_PACKET_PATH,
    WITNESS_PACKET_REVIEW_PATH,
    build_inventory_selection,
    build_maturation_index,
    build_mr_closeout_packet,
    build_mr_closeout_review,
    build_witness_attempt,
    build_witness_attempt_review,
    build_witness_packet,
    build_witness_packet_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_CHAIN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRPostMRMaturationExecution.lean"
)
LEAN_MATURATION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "TOEPostWitnessMaturationArtifacts.lean"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
V01_INDEX_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
)
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_post_mr_inventory_selection_is_discovered_and_deterministic() -> None:
    payload = _json(INVENTORY_SELECTION_PATH)
    assert payload == build_inventory_selection()
    assert payload["inventory_selection_classification"] == (
        "mathematical_regularity_inventory_exhausted_after_mr_assump_004"
    )
    assert payload["repo_authoritative_mathematical_regularity_row_inventory"] == ACCEPTED_MR_ROWS
    assert payload["remaining_mathematical_regularity_rows_after_mr_assump_004"] == []
    assert payload["inventory_exhausted_after_mr_assump_004"] is True
    assert payload["selected_next_target"] == (
        "prepare_qft_gr_mathematical_regularity_assumption_reduction_closeout_packet"
    )
    for value in payload["acceptance_criteria"].values():
        assert value is True


def test_mathematical_regularity_closeout_preserves_witness_pressure() -> None:
    packet = _json(MR_CLOSEOUT_PACKET_PATH)
    review = _json(MR_CLOSEOUT_REVIEW_PATH)
    assert packet == build_mr_closeout_packet()
    assert review == build_mr_closeout_review()
    assert packet["accepted_mathematical_regularity_assumption_rows"] == ACCEPTED_MR_ROWS
    assert review["closed_assumption_family"] == "mathematical_regularity_assumptions"
    assert review["remaining_mathematical_regularity_assumption_rows"] == []
    assert review["selected_next_target"] == POST_MR_WITNESS_PACKET_TARGET
    assert review["conservation_blocker_remains"] is True
    for key, value in review["non_claim_boundary"].items():
        assert value is False, key


def test_witness_reattempt_is_forced_and_routes_to_model_demonstration() -> None:
    packet = _json(WITNESS_PACKET_PATH)
    packet_review = _json(WITNESS_PACKET_REVIEW_PATH)
    attempt = _json(WITNESS_ATTEMPT_PATH)
    attempt_review = _json(WITNESS_ATTEMPT_REVIEW_PATH)
    assert packet == build_witness_packet()
    assert packet_review == build_witness_packet_review()
    assert attempt == build_witness_attempt()
    assert attempt_review == build_witness_attempt_review()
    assert attempt["result_classification"] == (
        "bounded_witness_inconclusive_requires_model_demonstration"
    )
    assert attempt["next_assumption_family_opened"] is False
    assert attempt_review["next_assumption_family_authorized"] is False
    assert attempt_review["selected_next_target"] == "prepare_toe_claim_ladder_artifact"
    for key, value in attempt_review["non_claim_boundary"].items():
        assert value is False, key


def test_maturation_artifacts_follow_witness_review_and_include_required_metadata() -> None:
    index = _json(MATURATION_INDEX_PATH)
    assert index == build_maturation_index()
    assert index["selected_next_target"] == FINAL_LIVE_TARGET
    expected_order = [
        "formal/docs/paper/TOE_CLAIM_LADDER_v0.md",
        "formal/docs/paper/TOE_CORE_HYPOTHESIS_v0.md",
        "formal/docs/paper/QFT_GR_MINIMAL_WORKING_MODEL_PROGRAM_v0.md",
        "formal/docs/paper/QFT_GR_COUNTERMODEL_REGISTRY_v0.json",
        "formal/docs/paper/TOE_FALSIFIER_AND_PREDICTION_REGISTRY_ADDENDUM_v0.md",
        "formal/docs/paper/TOE_EXPERT_TRANSLATION_LAYER_v0.md",
    ]
    assert index["artifact_order"] == expected_order

    required_fields = [
        "claim_level",
        "claim_ceiling",
        "scientific_role",
        "repo_status",
        "promotion_blockers",
        "physical_significance",
        "expert_legibility_gap",
        "falsifier_link",
        "countermodel_link",
    ]
    for path in [
        CLAIM_LADDER_PATH,
        CORE_HYPOTHESIS_PATH,
        MINIMAL_MODEL_PATH,
        FALSIFIER_ADDENDUM_PATH,
        EXPERT_TRANSLATION_PATH,
    ]:
        text = _read(path)
        for field in required_fields:
            assert f"`{field}`" in text

    registry = _json(COUNTERMODEL_REGISTRY_PATH)
    for field in required_fields:
        assert field in registry["metadata"]
    assert len(registry["countermodels"]) >= 3
    assert registry["promotion_allowed"] is False


def test_post_mr_chain_has_lean_and_authority_pointers() -> None:
    joined = "\n".join(
        _read(path)
        for path in [
            LEAN_CHAIN_PATH,
            LEAN_MATURATION_PATH,
            TOE_FORMAL_PATH,
            V01_INDEX_PATH,
            SURFACES_PATH,
            ROADMAP_PATH,
            REGISTRY_PATH,
            FRONTIER_PATH,
        ]
    )
    for token in [
        "QFT_GR_MATHEMATICAL_REGULARITY_ROW_INVENTORY_SELECTION_v0",
        "QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0",
        "QFT_GR_POST_MATHEMATICAL_REGULARITY_CONSERVED_SOURCE_WITNESS_REATTEMPT_RESULT_REVIEW_v0",
        "bounded_witness_inconclusive_requires_model_demonstration",
        "TOE_POST_WITNESS_MATURATION_INDEX_v0",
        "TOE_CLAIM_LADDER_v0",
        "QFT_GR_COUNTERMODEL_REGISTRY_v0",
        FINAL_LIVE_TARGET,
    ]:
        assert token in joined


def test_post_mr_maturation_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_post_mr_assump004_governed_maturation_gate.py"
    )
