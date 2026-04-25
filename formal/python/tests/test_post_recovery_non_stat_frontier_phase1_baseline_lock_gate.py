from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase1_baseline_lock_20260424_v0.json"
)
EXHAUSTION_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_post_der_cycle_exhaustion_readout_review_20260424_v0.json"
)
NON_REPLAY_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_non_replay_frontier_reassessment_20260424_v0.json"
)
NON_DER_SEARCH_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_non_der_theorem_row_candidate_search_design_20260424_v0.json"
)
COSMO_SR_BASELINE_STOP_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_cosmo_sr_negative_baseline_frontier_stop_20260424_v0.json"
)
RL10_LIMITATION_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "qm_stat_rl10_discrete_transition_bridge_limitation_review_20260422_v2.json"
)
GR_TRANCHE_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json"
)
QUEUE_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QUEUE_PRIORITY_NON_REPLAY_FRONTIER_RECONSTRUCTION_PACKET_20260423_v0.json"
)
QUEUE_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QUEUE_RECONSTRUCTION_DECLARED_NON_REPLAY_FRONTIER_SELECTION_20260423_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_non_stat_frontier_phase1_baseline_lock_gate() -> None:
    report = _read_json(REPORT_PATH)
    exhaustion = _read_json(EXHAUSTION_PATH)
    non_replay = _read_json(NON_REPLAY_PATH)
    non_der_search = _read_json(NON_DER_SEARCH_PATH)
    cosmo_sr_baseline_stop = _read_json(COSMO_SR_BASELINE_STOP_PATH)
    rl10_limitation = _read_json(RL10_LIMITATION_PATH)
    gr_tranche = _read_json(GR_TRANCHE_PATH)
    queue_packet = _read_json(QUEUE_PACKET_PATH)
    queue_selection = _read_json(QUEUE_SELECTION_PATH)

    assert report["schema_id"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE1_BASELINE_LOCK_20260424_v0"
    assert report["artifact_id"] == "post_recovery_non_stat_frontier_phase1_baseline_lock_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_NON_STAT_FRONTIER_PHASE1_BASELINE_LOCK_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_STAT_NON_DER_THEOREM_ROW_CANDIDATE_SEARCH_DESIGN"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_stat_non_der_theorem_row_candidate_search_design_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_PHASE1_BASELINE_LOCK"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["records_readout_only"] is True
    assert boundary["review_counts_theorem_gap_delta"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["gr_work_allowed"] is False
    assert boundary["rl10_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    # Cross-source baseline lock checks
    locked = report["baseline_locked_invariants"]
    assert locked["der01_cycle_closed_nonmoving"] is True
    assert locked["der02_cycle_closed_nonmoving"] is True
    assert locked["remaining_der_attempt_authorization"] == 0
    assert locked["stat_execution_held"] is True
    assert locked["stat_execution_authorization"] == "NONE"
    assert locked["stat_non_replay_frontier_opened"] is False
    assert locked["stat_new_non_der_candidate_declared"] is False
    assert locked["cosmo_sr_cycle08_negative_baseline_locked"] is True
    assert locked["cosmo_sr_materially_different_machine_pinned_candidate_present"] is False
    assert locked["rl10_branch_state"] == "LIMITATION_INTERPRETATION_SCOPE_HOLD"
    assert locked["rl10_one_more_bounded_comparator_cycle_justified"] is False
    assert (
        locked["gr_branch_state"]
        == "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED"
    )
    assert locked["gr_retry_path_status"] == "EXHAUSTED_AND_NONAUTHORITATIVE_FOR_NEXT_STEP_SELECTION"
    assert locked["theorem_gap_delta_counted"] == 0
    assert locked["fresh_movement_machine_pinned"] is False
    assert locked["packet05_bootstrap_authorized"] is False
    assert locked["seam_execution_allowed"] is False
    assert locked["master_action_allowed"] is False
    assert locked["promotion_or_closure_language_allowed"] is False

    assert exhaustion["readout_decision"]["der01_cycle_closed_nonmoving"] is True
    assert exhaustion["readout_decision"]["der02_cycle_closed_nonmoving"] is True
    assert exhaustion["readout_decision"]["any_remaining_der_attempt_authorization"] is False
    assert exhaustion["readout_decision"]["theorem_gap_delta_counted"] == 0
    assert exhaustion["readout_decision"]["fresh_movement_machine_pinned"] is False
    assert exhaustion["execution_hold_state"]["der_execution_authorization_available_now"] == "NONE"

    assert non_replay["decision"]["execution_held"] is True
    assert non_replay["decision"]["non_replay_execution_frontier_opened"] is False
    assert non_replay["decision"]["new_stat_theorem_row_candidate_declared"] is False

    assert non_der_search["known_state_checkpoint"]["remaining_der_attempt_authorization"] == 0
    assert non_der_search["known_state_checkpoint"]["execution_authorization"] == "NONE"
    assert non_der_search["current_search_readout"]["new_non_der_candidate_declared"] is False

    assert cosmo_sr_baseline_stop["cycle08_negative_baseline"]["terminal_outcome"] == "BLOCKER_UNCHANGED"
    assert (
        cosmo_sr_baseline_stop["alternative_hypothesis_review"][
            "machine_pinned_materially_different_cosmo_sr_candidate_found"
        ]
        is False
    )

    assert rl10_limitation["summary"]["review_outcome"] == "LIMITATION_INTERPRETATION_SCOPE_HOLD"
    assert rl10_limitation["summary"]["one_more_bounded_comparator_cycle_justified"] is False

    assert (
        gr_tranche["summary"]["terminal_outcome"]
        == "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED"
    )
    assert gr_tranche["summary"]["retry_path_status"] == "EXHAUSTED_AND_NONAUTHORITATIVE_FOR_NEXT_STEP_SELECTION"

    assert queue_packet["reconstruction_policy"]["execution_authorization"] == "NONE"
    assert queue_selection["selection_policy"]["required_reconstruction_execution_authorization"] == "NONE"

    phase_lock = report["phase_lock_contract"]
    assert phase_lock["phase"] == "PHASE_1_BASELINE_LOCK"
    assert phase_lock["required_for_phase2_candidate_intake"] is True
    assert phase_lock["phase2_entry_condition"] == "EXACT_MATCH_WITH_LOCKED_BASELINE_INVARIANTS"

    for token in (
        "EXECUTION_AUTHORIZATION_NONE",
        "DER_ATTEMPT_AUTHORIZATION_ZERO",
        "STAT_NON_REPLAY_FRONTIER_CLOSED",
        "COSMO_SR_CYCLE08_NEGATIVE_BASELINE_LOCKED",
        "RL10_LIMITATION_SCOPE_HOLD_LOCKED",
        "GR_DORMANT_RETRY_PATH_EXHAUSTED_LOCKED",
        "THEOREM_GAP_DELTA_COUNT_ZERO",
        "FRESH_MOVEMENT_MACHINE_PINNED_FALSE",
    ):
        assert token in phase_lock["baseline_token_set"]

    decision = report["decision"]
    assert decision["terminal_outcome"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE1_BASELINE_LOCK_COMPLETE"
    assert decision["phase1_baseline_lock_complete"] is True
    assert decision["execution_authorization"] == "NONE"
    assert decision["baseline_drift_detected"] is False

    for disallowed in (
        "rerun_der01_attempt_without_new_authorization",
        "rerun_der02_attempt_without_new_authorization",
        "count_theorem_gap_delta_without_machine_pinned_negative_delta",
        "open_packet05",
        "open_seam_work",
        "open_gr_work",
        "open_rl10_work",
        "invoke_master_action",
        "claim_promotion_or_closure",
    ):
        assert disallowed in report["disallowed_next_actions"]

    validation = report["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_non_stat_frontier_phase1_baseline_lock_gate.py" in validation["targeted_gate_command"]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})
