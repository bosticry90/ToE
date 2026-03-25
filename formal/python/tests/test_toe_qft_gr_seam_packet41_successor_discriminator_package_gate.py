from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
PACKAGE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_v0.md"
PACKAGE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_successor_discriminator_package_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MEASUREMENT_PROTOCOL_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_numeric_threshold_measurement_protocol_checkpoint_v0.json"
SCORECARD_CYCLE01_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle01_checkpoint_v0.json"
PACKET41_AUTH_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET41_AUTHORIZATION_v0.md"
PACKET41_AUTH_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_authorization_checkpoint_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _extract_token_from_compact_state_or_inventory(state_text: str, inventory_text: str, token_name: str) -> str:
    if re.search(rf"\b{re.escape(token_name)}\s*:\s*", state_text):
        return _extract_token(state_text, token_name)
    return _extract_token(inventory_text, token_name)


def test_packet41_successor_discriminator_package_document_structure() -> None:
    text = _read(PACKAGE_DOC_PATH)
    required_markers = [
        "Package ID:",
        "Parent eligibility review:",
        "Parent targeted justification review:",
        "## Concrete Successor Discriminator Definition",
        "## Required Statement Layer (Cycle02 Numeric-Evaluated, Review-Layer Pending)",
        "## Admissible Numeric Measurement Readiness",
        "required_numeric_fields_status: PRESENT_FROM_ADMISSIBLE_CHECKPOINTS_v0",
        "scorecard_cycle01_outcome_status: HOLD_RETAINED_DUE_TO_MISSING_ADMISSIBLE_NUMERIC_INPUTS_v0",
        "scorecard_cycle02_outcome_status: HOLD_RETAINED_DUE_TO_REVIEW_LAYER_FAILURE_v0",
        "release_clearance_status: NOT_CLEARED_REVIEW_LAYER_STACK_PENDING_v0",
        "TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_STATUS_v0: DEFINED_NUMERICALLY_EVALUATED_CYCLE02_REVIEW_LAYER_CLEARANCE_PENDING_v0",
        "TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_OUTCOME_v0: HOLD_RETAINED_REVIEW_LAYER_CLEARANCE_PENDING_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Packet41 successor package doc missing marker: {marker}"


def test_packet41_successor_discriminator_package_checkpoint_schema() -> None:
    artifact = _read_json(PACKAGE_CHECKPOINT_PATH)
    protocol = _read_json(MEASUREMENT_PROTOCOL_CHECKPOINT_PATH)
    cycle01 = _read_json(SCORECARD_CYCLE01_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet41_successor_discriminator_package_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2W_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE"
    assert artifact.get("status") == "PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_NUMERICALLY_EVALUATED_HOLD_v0"

    payload = artifact.get("payload", {})
    assert payload.get("package_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_v0.md"
    assert payload.get("parent_scorecard_cycle02_checkpoint_path") == (
        "formal/output/toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0.json"
    )
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    definition = payload.get("successor_discriminator_definition", {})
    assert definition.get("successor_discriminator_id") == "packet41_post_refutation_resilience_closure_stability_discriminator_v0"

    statements = payload.get("required_statement_layer", {})
    assert statements.get("seam_level_gain_statement_status") == "NUMERICALLY_EVALUATED_CYCLE02_REVIEW_LAYER_CLEARANCE_PENDING_v0"
    assert statements.get("residual_ambiguity_reduction_statement_status") == "NUMERICALLY_EVALUATED_CYCLE02_REVIEW_LAYER_CLEARANCE_PENDING_v0"
    assert statements.get("objective_distance_reduction_statement_status") == "NUMERICALLY_EVALUATED_CYCLE02_REVIEW_LAYER_CLEARANCE_PENDING_v0"
    assert statements.get("stagnation_clearance_statement_status") == "NUMERICALLY_EVALUATED_CYCLE02_REVIEW_LAYER_CLEARANCE_PENDING_v0"

    readiness = payload.get("numeric_measurement_readiness", {})
    assert readiness.get("required_numeric_fields_status") == "PRESENT_FROM_ADMISSIBLE_CHECKPOINTS_v0"
    assert readiness.get("scorecard_cycle01_outcome_status") == "HOLD_RETAINED_DUE_TO_MISSING_ADMISSIBLE_NUMERIC_INPUTS_v0"
    assert readiness.get("scorecard_cycle02_outcome_status") == "HOLD_RETAINED_DUE_TO_REVIEW_LAYER_FAILURE_v0"
    assert readiness.get("release_clearance_status") == "NOT_CLEARED_REVIEW_LAYER_STACK_PENDING_v0"

    cycle01_payload = cycle01.get("payload", {})
    cycle01_thresholds = cycle01_payload.get("threshold_pass", {})
    assert readiness.get("scorecard_cycle01_outcome_status") == cycle01_payload.get("evaluation_outcome")
    assert cycle01_thresholds.get("threshold_4_pass") is False
    assert cycle01_payload.get("authorization_artifact_creation") == "FORBIDDEN_v0"

    protocol_hold = protocol.get("payload", {}).get("hold_policy", {})
    assert protocol_hold.get("automatic_release_without_threshold_4_pass") == "FORBIDDEN_v0"
    assert protocol_hold.get("packet41_authorization_freeze_status") == "ENFORCED_v0"

    hold = payload.get("hold_policy_alignment", {})
    assert hold.get("packet41_authorization_freeze_status") == "ENFORCED_v0"
    assert hold.get("release_without_admissible_numeric_measurement") == "FORBIDDEN_v0"


def test_packet41_successor_discriminator_package_authority_parity_and_hold_freeze() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_v0.md",
        "formal/output/toe_qft_gr_seam_packet41_successor_discriminator_package_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet41_successor_discriminator_package_gate.py",
    ]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing packet41 successor package pointer in compact-State or inventory: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet41 successor package pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        "TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_STATUS_v0",
    )
    roadmap_status = _extract_token(
        roadmap_text,
        "TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_STATUS_v0",
    )
    assert state_status == roadmap_status == "DEFINED_NUMERICALLY_EVALUATED_CYCLE02_REVIEW_LAYER_CLEARANCE_PENDING_v0"

    state_outcome = _extract_token_from_compact_state_or_inventory(
        state_text,
        inventory_text,
        "TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_OUTCOME_v0",
    )
    roadmap_outcome = _extract_token(
        roadmap_text,
        "TOE_QFT_GR_SEAM_PACKET41_SUCCESSOR_DISCRIMINATOR_PACKAGE_OUTCOME_v0",
    )
    assert state_outcome == roadmap_outcome == "HOLD_RETAINED_REVIEW_LAYER_CLEARANCE_PENDING_v0"

    assert not PACKET41_AUTH_DOC_PATH.exists(), "Packet41 authorization doc must not exist while successor package is pending numeric clearance"
    assert not PACKET41_AUTH_CHECKPOINT_PATH.exists(), "Packet41 authorization checkpoint must not exist while successor package is pending numeric clearance"
