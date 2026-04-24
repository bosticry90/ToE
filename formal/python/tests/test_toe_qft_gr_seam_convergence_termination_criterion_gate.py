from __future__ import annotations

import json
import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
CRITERION_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
CRITERION_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json"
OBJECTIVE_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_REACTIVATION_OBJECTIVE_v0.md"
OBJECTIVE_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_reactivation_objective_checkpoint_v0.json"
ASSESSMENT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md"
ASSESSMENT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet40_assessment_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
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


def _extract_token_from_surfaces(texts: list[str], token_name: str) -> str:
    for text in texts:
        m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
        if m is not None:
            return m.group(1)
    raise AssertionError(f"Missing token `{token_name}` across authority surfaces.")


def test_qft_gr_seam_convergence_criterion_document_structure() -> None:
    text = _read(CRITERION_DOC_PATH)
    required_markers = [
        "Criterion ID:",
        "Parent objective:",
        "Parent assessment anchor:",
        "## Fixed End States",
        "## Seam-Level Progress Metric",
        "## Marginal-Gain Threshold",
        "## Stagnation Test",
        "stagnation_result_status: HOLD_FORK_OR_TERMINATE_REQUIRED_v0",
        "## Anti-Infinite-Ladder Rule",
        "local_progress_is_necessary_but_not_sufficient: ENFORCED_v0",
        "narrative_momentum_authorization: FORBIDDEN_v0",
        "## Mandatory Disposition Rule",
        "## Future Packet41 Authorization Binding",
        "required_parent_assessment_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md",
        "required_convergence_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md",
        "required_packet41_eligibility_review_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md",
        "required_packet41_targeted_justification_review_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_TARGETED_JUSTIFICATION_REVIEW_v0.md",
        "required_packet41_hold_fork_decision_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_v0.md",
        "required_packet41_retrospective_cumulative_delta_audit_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_v0.md",
        "required_packet41_reconsideration_numeric_thresholds_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md",
        "required_packet41_numeric_threshold_measurement_protocol_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md",
        "required_packet41_reconsideration_scorecard_worksheet_doc_path: formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md",
        "packet41_authorization_status: FROZEN_PENDING_CONVERGENCE_BINDING_v0",
        "TOE_QFT_GR_SEAM_CONVERGENCE_STATUS_v0: ACTIVE_CONVERGENCE_GUARDRAIL_ENFORCED_v0",
        "TOE_QFT_GR_SEAM_PACKET41_AUTHORIZATION_POLICY_v0: FROZEN_UNTIL_CONVERGENCE_BINDING_SATISFIED_v0",
        "TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_GATE_v0: REQUIRED_CONVERGENCE_SCHEMA_AND_FUTURE_AUTHORIZATION_BINDING",
        "QFT_GR_SEAM_FORK_DECISION_STATUS_v0: HOLD_FOR_SCALAR_PUBLICATION_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Convergence criterion doc missing marker: {marker}"


def test_qft_gr_seam_convergence_checkpoint_schema_and_current_disposition() -> None:
    artifact = _read_json(CRITERION_CHECKPOINT_PATH)
    objective_artifact = _read_json(OBJECTIVE_CHECKPOINT_PATH)
    assessment_artifact = _read_json(ASSESSMENT_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2T_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION"
    assert artifact.get("status") == "SEAM_CONVERGENCE_TERMINATION_CRITERION_ACTIVE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("criterion_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
    assert payload.get("current_program_anchor_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md"
    assert payload.get("current_program_anchor_checkpoint_path") == "formal/output/toe_qft_gr_seam_packet40_assessment_checkpoint_v0.json"
    assert payload.get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"

    fixed = payload.get("fixed_end_states", {})
    assert fixed.get("seam_discharged") == "ALLOWED_v0"
    assert fixed.get("seam_held") == "ALLOWED_v0"
    assert fixed.get("seam_forked") == "ALLOWED_v0"
    assert fixed.get("seam_terminated_as_nonproductive") == "ALLOWED_v0"
    assert fixed.get("indefinite_packet_extension_without_measurable_seam_level_gain") == "FORBIDDEN_v0"

    progress = payload.get("seam_level_progress_metric", {})
    assert progress.get("discriminator_strength_increase") == "REQUIRED_v0"
    assert progress.get("residual_ambiguity_decrease") == "REQUIRED_v0"
    assert progress.get("remaining_gap_narrowing") == "REQUIRED_v0"
    assert progress.get("objective_distance_reduction") == "REQUIRED_v0"

    threshold = payload.get("marginal_gain_threshold", {})
    assert threshold.get("future_packet_must_exceed_local_narrowing_only") == "PASS_REQUIRED_v0"
    assert threshold.get("future_packet_must_improve_seam_level_closure_prospects") == "PASS_REQUIRED_v0"

    stagnation = payload.get("stagnation_test", {})
    assert stagnation.get("stagnation_result_status") == "HOLD_FORK_OR_TERMINATE_REQUIRED_v0"

    binding = payload.get("future_packet41_authorization_binding", {})
    assert binding.get("required_parent_assessment_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md"
    assert binding.get("required_convergence_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md"
    assert binding.get("required_packet41_eligibility_review_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md"
    assert binding.get("required_packet41_targeted_justification_review_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_TARGETED_JUSTIFICATION_REVIEW_v0.md"
    assert binding.get("required_packet41_hold_fork_decision_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_v0.md"
    assert binding.get("required_packet41_retrospective_cumulative_delta_audit_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_v0.md"
    assert binding.get("required_packet41_reconsideration_numeric_thresholds_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md"
    assert binding.get("required_packet41_numeric_threshold_measurement_protocol_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md"
    assert binding.get("required_packet41_reconsideration_scorecard_worksheet_doc_path") == "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md"
    assert binding.get("packet41_must_clear_marginal_gain_threshold") == "YES_v0"
    assert binding.get("packet41_must_clear_stagnation_test") == "YES_v0"
    assert binding.get("packet41_must_carry_review_disposition_release_from_hold") == "YES_v0"
    assert binding.get("packet41_must_clear_targeted_justification_review") == "YES_v0"
    assert binding.get("packet41_must_clear_hold_fork_decision_release_condition") == "YES_v0"
    assert binding.get("packet41_must_clear_retrospective_cumulative_delta_audit_release_condition") == "YES_v0"
    assert binding.get("packet41_must_clear_reconsideration_numeric_thresholds_release_condition") == "YES_v0"
    assert binding.get("packet41_must_clear_numeric_threshold_measurement_protocol_release_condition") == "YES_v0"
    assert binding.get("packet41_must_clear_reconsideration_scorecard_worksheet_release_condition") == "YES_v0"

    disposition = payload.get("current_program_disposition", {})
    assert disposition.get("current_packet_ceiling_without_new_binding") == "PACKET40_ASSESSMENT_COMPLETE_v0"
    assert disposition.get("packet41_authorization_status") == "FROZEN_PENDING_CONVERGENCE_BINDING_v0"

    assert objective_artifact.get("payload", {}).get("active_seam_question") == "stress_energy_to_weak_curvature_handoff_strengthening"
    assert assessment_artifact.get("status") == "PACKET40_ASSESSMENT_COMPLETE_CONDITIONAL_PACKET41_READINESS_ONLY_v0"


def test_qft_gr_seam_convergence_authority_parity_and_future_packet41_binding() -> None:
    criterion_text = _read(CRITERION_DOC_PATH)
    objective_text = _read(OBJECTIVE_DOC_PATH)
    assessment_text = _read(ASSESSMENT_DOC_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    q = "stress_energy_to_weak_curvature_handoff_strengthening"
    assert q in criterion_text
    assert q in objective_text
    assert q in assessment_text

    refs = [
        "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md",
        "formal/output/toe_qft_gr_seam_convergence_termination_criterion_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_convergence_termination_criterion_gate.py",
    ]
    for ref in refs:
        assert any(ref in text for text in (state_text, inventory_text, roadmap_text)), (
            f"Missing convergence pointer across authority surfaces: {ref}"
        )
        assert ref in roadmap_text, f"Missing convergence pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text], "TOE_QFT_GR_SEAM_CONVERGENCE_STATUS_v0"
    )
    roadmap_status = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_CONVERGENCE_STATUS_v0")
    assert state_status == roadmap_status == "ACTIVE_CONVERGENCE_GUARDRAIL_ENFORCED_v0"

    state_policy = _extract_token_from_surfaces(
        [state_text, inventory_text, roadmap_text], "TOE_QFT_GR_SEAM_PACKET41_AUTHORIZATION_POLICY_v0"
    )
    roadmap_policy = _extract_token(roadmap_text, "TOE_QFT_GR_SEAM_PACKET41_AUTHORIZATION_POLICY_v0")
    assert state_policy == roadmap_policy == "FROZEN_UNTIL_CONVERGENCE_BINDING_SATISFIED_v0"

    if PACKET41_AUTH_DOC_PATH.exists():
        packet41_text = _read(PACKET41_AUTH_DOC_PATH)
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md" in packet41_text
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md" in packet41_text
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md" in packet41_text
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_TARGETED_JUSTIFICATION_REVIEW_v0.md" in packet41_text
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_v0.md" in packet41_text
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_v0.md" in packet41_text
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md" in packet41_text
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md" in packet41_text
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md" in packet41_text

    if PACKET41_AUTH_CHECKPOINT_PATH.exists():
        packet41_artifact = _read_json(PACKET41_AUTH_CHECKPOINT_PATH)
        packet41_payload = packet41_artifact.get("payload", {})
        values = json.dumps(packet41_payload)
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md" in values
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md" in values
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_ELIGIBILITY_REVIEW_v0.md" in values
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_TARGETED_JUSTIFICATION_REVIEW_v0.md" in values
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_HOLD_FORK_DECISION_v0.md" in values
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_RETROSPECTIVE_CUMULATIVE_DELTA_AUDIT_v0.md" in values
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_NUMERIC_THRESHOLDS_v0.md" in values
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md" in values
        assert "formal/docs/paper/TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_WORKSHEET_v0.md" in values