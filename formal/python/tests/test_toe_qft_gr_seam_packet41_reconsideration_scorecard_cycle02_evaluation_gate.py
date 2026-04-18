from __future__ import annotations

import fnmatch
import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
EVALUATION_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0.json"
WORKSHEET_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_reconsideration_scorecard_worksheet_checkpoint_v0.json"
MEASUREMENT_PROTOCOL_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_numeric_threshold_measurement_protocol_checkpoint_v0.json"
NUMERIC_THRESHOLDS_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_reconsideration_numeric_thresholds_checkpoint_v0.json"
ELIGIBILITY_REVIEW_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_eligibility_review_checkpoint_v0.json"
TARGETED_JUSTIFICATION_REVIEW_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_targeted_justification_review_checkpoint_v0.json"
HOLD_FORK_DECISION_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_packet41_hold_fork_decision_checkpoint_v0.json"
RETROSPECTIVE_AUDIT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_gr_seam_retrospective_cumulative_delta_audit_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_packet41_scorecard_cycle02_authority_parity() -> None:
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    refs = [
        "formal/output/toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_gr_seam_packet41_reconsideration_scorecard_cycle02_evaluation_gate.py",
    ]
    for ref in refs:
        assert ref in state_text or ref in inventory_text, (
            f"Missing packet41 cycle02 scorecard pointer in compact-State or inventory: {ref}"
        )
        assert ref in roadmap_text, f"Missing packet41 cycle02 scorecard pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    status_token = (
        "TOE_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_CYCLE02_STATUS_v0: "
        "EVALUATED_HOLD_RETAINED_REVIEW_LAYER_FAILURE_v0"
    )
    assert status_token in roadmap_text
    assert status_token in state_text or status_token in inventory_text


def test_packet41_scorecard_cycle02_checkpoint_schema_and_values() -> None:
    artifact = _read_json(EVALUATION_CHECKPOINT_PATH)
    worksheet = _read_json(WORKSHEET_CHECKPOINT_PATH)
    protocol = _read_json(MEASUREMENT_PROTOCOL_CHECKPOINT_PATH)
    numeric_thresholds = _read_json(NUMERIC_THRESHOLDS_CHECKPOINT_PATH)
    eligibility_review = _read_json(ELIGIBILITY_REVIEW_CHECKPOINT_PATH)
    targeted_review = _read_json(TARGETED_JUSTIFICATION_REVIEW_CHECKPOINT_PATH)
    hold_fork = _read_json(HOLD_FORK_DECISION_CHECKPOINT_PATH)
    retrospective_audit = _read_json(RETROSPECTIVE_AUDIT_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_gr_seam_packet41_reconsideration_scorecard_evaluation_cycle02_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2ZB_QFT_GR_SEAM_PACKET41_RECONSIDERATION_SCORECARD_EVALUATION_CYCLE02"
    assert artifact.get("status") == "PACKET41_RECONSIDERATION_SCORECARD_EVALUATION_CYCLE02_COMPLETE_HOLD_v0"

    payload = artifact.get("payload", {})
    assert payload.get("formula_version") == "packet41_measurement_protocol_v0"

    worksheet_schema = worksheet.get("payload", {}).get("worksheet_schema", {})

    availability = payload.get("input_field_availability", {})
    required_inputs = worksheet_schema.get("required_inputs", [])
    expected_availability_keys = {name for name in required_inputs if name != "cycle_id"}
    assert set(availability.keys()) == expected_availability_keys
    assert all(v is True for v in availability.values())

    values = payload.get("scorecard_values", {})
    computed_fields = worksheet_schema.get("computed_fields", [])
    expected_value_keys = expected_availability_keys | set(computed_fields)
    assert set(values.keys()) == expected_value_keys

    d_prev = values["D_prev"]
    a_prev = values["A_prev"]
    o_prev = values["O_prev"]
    d_curr = values["D_curr"]
    a_curr = values["A_curr"]
    o_curr = values["O_curr"]
    n_curr = values["N_curr"]

    g_prev = 0.5 * d_prev + 0.3 * a_prev + 0.2 * o_prev
    g_curr = 0.5 * d_curr + 0.3 * a_curr + 0.2 * o_curr
    s_value = max(0.0, (g_prev - g_curr) / max(g_prev, 1e-6))
    m_value = 0.5 * n_curr + 0.3 * max(0.0, a_prev - a_curr) + 0.2 * max(0.0, o_prev - o_curr)
    streak3 = values["I_stag_curr"] + values["I_stag_prev"] + values["I_stag_prev2"]

    assert abs(values["G_prev"] - g_prev) < 1e-9
    assert abs(values["G_curr"] - g_curr) < 1e-9
    assert abs(values["S_value"] - s_value) < 1e-9
    assert abs(values["M_value"] - m_value) < 1e-9
    assert values["Streak3_value"] == streak3

    numeric_threshold_payload = numeric_thresholds.get("payload", {})
    threshold_cfg = numeric_threshold_payload.get("numeric_thresholds", {})
    min_shrinkage = threshold_cfg.get("min_seam_gap_shrinkage_fraction", {}).get("required_minimum")
    min_marginal_gain = threshold_cfg.get("min_marginal_gain_index", {}).get("required_minimum")
    max_stagnation_streak = threshold_cfg.get("max_consecutive_stagnant_packets", {}).get("required_maximum")
    assert isinstance(min_shrinkage, (int, float))
    assert isinstance(min_marginal_gain, (int, float))
    assert isinstance(max_stagnation_streak, (int, float))

    expected_threshold_1_pass = s_value >= float(min_shrinkage)
    expected_threshold_2_pass = m_value >= float(min_marginal_gain)
    expected_threshold_3_pass = streak3 <= int(max_stagnation_streak)

    thresholds = payload.get("threshold_pass", {})
    assert thresholds.get("threshold_1_pass") is expected_threshold_1_pass
    assert thresholds.get("threshold_2_pass") is expected_threshold_2_pass
    assert thresholds.get("threshold_3_pass") is expected_threshold_3_pass

    review_layer = payload.get("review_layer_pass", {})
    expected_eligibility_pass = eligibility_review.get("status") == "PACKET41_ELIGIBILITY_REVIEW_COMPLETE_AUTHORIZE_v0"
    expected_targeted_pass = targeted_review.get("status") == "PACKET41_TARGETED_JUSTIFICATION_REVIEW_COMPLETE_SUFFICIENT_v0"
    expected_hold_fork_release_pass = (
        hold_fork.get("status") == "PACKET41_HOLD_FORK_DECISION_COMPLETE_RELEASE_v0"
    )
    expected_retrospective_release_pass = (
        retrospective_audit.get("payload", {})
        .get("program_level_classification", {})
        .get("packet41_reopen_readiness")
        == "READY_v0"
    )

    assert review_layer.get("packet41_eligibility_review_pass") is expected_eligibility_pass
    assert review_layer.get("packet41_targeted_justification_review_pass") is expected_targeted_pass
    assert review_layer.get("packet41_hold_fork_release_condition_pass") is expected_hold_fork_release_pass
    assert review_layer.get("retrospective_cumulative_delta_audit_release_condition_pass") is expected_retrospective_release_pass

    expected_existing_review_layers_pass = all(
        (
            expected_eligibility_pass,
            expected_targeted_pass,
            expected_hold_fork_release_pass,
            expected_retrospective_release_pass,
        )
    )
    assert payload.get("existing_review_layers_pass") is expected_existing_review_layers_pass

    expected_threshold_4_pass = (
        expected_threshold_1_pass
        and expected_threshold_2_pass
        and expected_threshold_3_pass
        and expected_existing_review_layers_pass
    )
    assert thresholds.get("threshold_4_pass") is expected_threshold_4_pass
    assert thresholds.get("auto_fail_reason") == "REVIEW_LAYER_STACK_NOT_CLEARED_v0"

    expected_review_layer_fields = set(worksheet_schema.get("review_layer_fields", []))
    assert set(review_layer.keys()) == expected_review_layer_fields

    active_seam_question = numeric_threshold_payload.get("active_seam_question")
    assert active_seam_question == "stress_energy_to_weak_curvature_handoff_strengthening"
    assert eligibility_review.get("payload", {}).get("active_seam_question") == active_seam_question
    assert targeted_review.get("payload", {}).get("active_seam_question") == active_seam_question
    assert hold_fork.get("payload", {}).get("active_seam_question") == active_seam_question
    assert retrospective_audit.get("payload", {}).get("active_seam_question") == active_seam_question
    assert payload.get("disposition_recommendation") == "HOLD_RETAINED_v0"
    assert payload.get("authorization_artifact_creation") == "FORBIDDEN_v0"


def test_packet41_scorecard_cycle02_evidence_sources_are_admissible() -> None:
    artifact = _read_json(EVALUATION_CHECKPOINT_PATH)
    protocol = _read_json(MEASUREMENT_PROTOCOL_CHECKPOINT_PATH)

    evidence_sources = artifact.get("payload", {}).get("evidence_sources_used", [])
    admissible_patterns = protocol.get("payload", {}).get("admissible_evidence_surfaces", [])

    assert evidence_sources
    for source in evidence_sources:
        assert any(fnmatch.fnmatch(source, pattern) for pattern in admissible_patterns), (
            f"Non-admissible evidence source in cycle02 scorecard evaluation payload: {source}"
        )
