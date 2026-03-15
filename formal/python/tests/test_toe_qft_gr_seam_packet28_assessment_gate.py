from __future__ import annotations

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]

DOC = ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET28_ASSESSMENT_v0.md"
CHECKPOINT = (
    ROOT
    / "formal"
    / "output"
    / "toe_qft_gr_seam_packet28_assessment_checkpoint_v0.json"
)
PARENT_EXEC_DOC = (
    ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_QFT_GR_SEAM_PACKET28_BOUNDED_EXECUTION_v0.md"
)
PARENT_EXEC_CHECKPOINT = (
    ROOT
    / "formal"
    / "output"
    / "toe_qft_gr_seam_packet28_bounded_execution_checkpoint_v0.json"
)
PARENT_AUTH_DOC = (
    ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_QFT_GR_SEAM_PACKET28_AUTHORIZATION_v0.md"
)
PARENT_AUTH_CHECKPOINT = (
    ROOT
    / "formal"
    / "output"
    / "toe_qft_gr_seam_packet28_authorization_checkpoint_v0.json"
)


EXPECTED_TARGET = (
    "freeze_one_bounded_handoff_post_endurance_closure_durability_discriminator_"
    "that_maps_packet27_closure_endurance_witness_to_a_single_non_scalar_expanding_"
    "closure_durability_witness"
)

EXPECTED_PACKET29_TARGET = (
    "freeze_one_bounded_handoff_post_durability_closure_stability_discriminator_"
    "that_maps_packet28_closure_durability_witness_to_a_single_non_scalar_expanding_"
    "closure_stability_witness"
)


def _read_text(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _load_json(path: Path) -> dict:
    return json.loads(_read_text(path))


def test_packet28_assessment_files_exist() -> None:
    assert DOC.exists(), f"Missing packet28 assessment doc: {DOC}"
    assert CHECKPOINT.exists(), f"Missing packet28 assessment checkpoint: {CHECKPOINT}"


def test_packet28_assessment_doc_required_markers() -> None:
    text = _read_text(DOC)
    required_markers = [
        "# TOE QFT-GR Seam Packet28 Assessment v0",
        "## Assessment Questions",
        "## Objective Progress Snapshot",
        "## Scalar Freeze Compliance",
        "## Decision Rule Projection (for packet29 authorization)",
        "TOE_QFT_GR_SEAM_PACKET28_ASSESSMENT_STATUS_v0: ASSESSED_TARGET_SATISFACTION_VERIFIED_v0",
        "PACKET28_ASSESSMENT_COMPLETE_v0",
        "NO_SCALAR_BASELINE_DRIFT_v0",
        "NO_BACKFLOW_DETECTED_v0",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
        "GENUINE_PHYSICS_PROGRESS_IF_SINGLE_BOUNDED_TARGET_v0",
        "REJECT_IF_MOMENTUM_EXTENSION_v0",
        EXPECTED_TARGET,
        EXPECTED_PACKET29_TARGET,
    ]
    for marker in required_markers:
        assert marker in text, f"Missing doc marker: {marker}"


def test_packet28_assessment_checkpoint_schema_and_lineage() -> None:
    data = _load_json(CHECKPOINT)
    assert data["artifact_id"] == "toe_qft_gr_seam_packet28_assessment_checkpoint_v0"
    assert data["phase"] == "PHASE_2B_QFT_GR_SEAM_PACKET28_ASSESSMENT"
    assert data["scope"] == "packet28_target_satisfaction_assessment"
    assert data["status"] == "PACKET28_ASSESSMENT_COMPLETE_v0"

    payload = data["payload"]
    assert payload["assessment_doc_path"].endswith(
        "TOE_QFT_GR_SEAM_PACKET28_ASSESSMENT_v0.md"
    )
    assert payload["parent_packet_doc_path"].endswith(
        "TOE_QFT_GR_SEAM_PACKET28_BOUNDED_EXECUTION_v0.md"
    )
    assert payload["parent_packet_checkpoint_path"].endswith(
        "toe_qft_gr_seam_packet28_bounded_execution_checkpoint_v0.json"
    )
    assert payload["parent_authorization_doc_path"].endswith(
        "TOE_QFT_GR_SEAM_PACKET28_AUTHORIZATION_v0.md"
    )
    assert payload["parent_authorization_checkpoint_path"].endswith(
        "toe_qft_gr_seam_packet28_authorization_checkpoint_v0.json"
    )

    assert payload["active_seam_question"] == (
        "stress_energy_to_weak_curvature_handoff_strengthening"
    )


def test_packet28_assessment_target_satisfaction_and_packet29_rule() -> None:
    payload = _load_json(CHECKPOINT)["payload"]
    ts = payload["target_satisfaction"]
    assert ts["authorized_exact_target"] == EXPECTED_TARGET
    assert ts["satisfied"] is True
    assert ts["verdict"] == "YES_EXACT_TARGET_SATISFIED_v0"

    packet29 = payload["packet29_decision"]
    assert packet29["authorized"] is True
    assert packet29["progress_verdict"] == "GENUINE_PHYSICS_PROGRESS_IF_SINGLE_BOUNDED_TARGET_v0"
    assert packet29["ladder_extension_verdict"] == "REJECT_IF_MOMENTUM_EXTENSION_v0"
    assert packet29["verdict"] == "JUSTIFIED_CONDITIONAL_ON_SINGLE_BOUNDED_TARGET_v0"
    assert packet29["exact_bounded_target"] == EXPECTED_PACKET29_TARGET
    assert packet29["hold_refine_trigger_status"] == "NOT_HIT_v0"


def test_packet28_assessment_scalar_and_guardrail_invariants() -> None:
    payload = _load_json(CHECKPOINT)["payload"]
    scalar = payload["scalar_compliance"]
    assert scalar["scalar_drift_status"] == "NO_SCALAR_BASELINE_DRIFT_v0"
    assert scalar["scalar_scope_backflow_status"] == "NO_BACKFLOW_DETECTED_v0"

    projection = payload["decision_rule_projection"]
    assert projection["scalar_scope_backflow_status"] == "NO_BACKFLOW_DETECTED_v0"
    assert projection["momentum_extension_rejection_status"] == "ENFORCED_v0"

    guardrails = payload["guardrails"]
    assert guardrails["seam_fork_decision_status"] == (
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0"
    )
    assert guardrails["assessment_scope"] == "ASSESS_PACKET28_BEFORE_PACKET29_v0"


def test_packet28_assessment_parent_chain_exists() -> None:
    assert PARENT_EXEC_DOC.exists(), f"Missing parent execution doc: {PARENT_EXEC_DOC}"
    assert PARENT_EXEC_CHECKPOINT.exists(), (
        f"Missing parent execution checkpoint: {PARENT_EXEC_CHECKPOINT}"
    )
    assert PARENT_AUTH_DOC.exists(), f"Missing parent authorization doc: {PARENT_AUTH_DOC}"
    assert PARENT_AUTH_CHECKPOINT.exists(), (
        f"Missing parent authorization checkpoint: {PARENT_AUTH_CHECKPOINT}"
    )

    parent_exec_payload = _load_json(PARENT_EXEC_CHECKPOINT)["payload"]
    assert (
        parent_exec_payload["authorized_target_binding"]["authorized_exact_target"]
        == EXPECTED_TARGET
    )
