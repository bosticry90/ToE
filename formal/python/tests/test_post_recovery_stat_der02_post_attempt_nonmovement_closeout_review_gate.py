from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CLOSEOUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_post_attempt_nonmovement_closeout_review_20260424_v0.json"
)
EXECUTION_PACKET_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_bounded_discharge_attempt_execution_packet_v0.json"
)
AUTHORIZATION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_discharge_attempt_authorization_readiness_review_20260424_v0.json"
)
STAT_EVIDENCE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json"
)
QUALIFICATION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json"
)
PACKET05_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_packet05_lane_eligibility_review_20260420_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_stat_der02_post_attempt_nonmovement_closeout_review_gate() -> None:
    closeout = _read_json(CLOSEOUT_PATH)
    execution = _read_json(EXECUTION_PACKET_PATH)
    authorization = _read_json(AUTHORIZATION_REPORT_PATH)
    evidence = _read_json(STAT_EVIDENCE_REPORT_PATH)
    qualification = _read_json(QUALIFICATION_REPORT_PATH)
    packet05 = _read_json(PACKET05_REPORT_PATH)

    assert closeout["schema_id"] == "POST_RECOVERY_STAT_DER02_POST_ATTEMPT_NONMOVEMENT_CLOSEOUT_REVIEW_20260424_v0"
    assert closeout["artifact_id"] == "post_recovery_stat_der02_post_attempt_nonmovement_closeout_review_20260424_v0"
    assert closeout["status"] == "POST_RECOVERY_DER02_POST_ATTEMPT_NONMOVEMENT_CLOSEOUT_REVIEW_NONCLAIM"

    trigger = closeout["trigger"]
    assert trigger["source"] == "DER02_ONE_BOUNDED_DISCHARGE_ATTEMPT_CONSUMED"
    assert trigger["execution_packet"] == "formal/output/stat_der02_bounded_discharge_attempt_execution_packet_v0.json"

    boundary = closeout["frontier_boundary"]
    assert boundary["mode"] == "POST_ATTEMPT_NONMOVEMENT_CLOSEOUT"
    assert boundary["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert boundary["additional_der02_attempt_authorized"] is False
    assert boundary["new_execution_packet_authored_by_this_review"] is False
    assert boundary["theorem_gap_delta_counted"] == 0
    assert boundary["stat_packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["gr_work_allowed"] is False
    assert boundary["rl10_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    cycle = closeout["attempt_cycle_state"]
    assert cycle["one_bounded_attempt_authorized"] is True
    assert cycle["one_bounded_attempt_executed"] is True
    assert cycle["authorized_attempt_consumed"] is True
    assert cycle["remaining_der02_discharge_attempt_authorization"] == 0
    assert cycle["terminal_outcome"] == execution["payload"]["execution_packet_result"]
    assert cycle["terminal_outcome"] == "STAT_DER02_BOUNDED_DISCHARGE_ATTEMPT_BLOCKER_UNCHANGED"

    readout = closeout["nonmovement_readout"]
    assert readout["blocker_reduction_counted_now"] is False
    assert readout["machine_pinned_negative_theorem_gap_delta"] is False
    assert readout["theorem_gap_delta"] == 0
    assert readout["theorem_gap_delta_counted"] == 0
    assert readout["fresh_movement_machine_pinned"] is False
    assert readout["der02_discharge_claimed"] is False
    assert readout["promotion_earned"] is False
    assert readout["stat_evidence_surface_terminal_outcome"] == evidence["summary"]["terminal_outcome"]
    assert readout["theorem_gap_fresh_movement_qualification_selected_row"] == qualification["summary"]["selected_row"]
    assert readout["packet05_eligible_for_bootstrap"] == packet05["summary"]["eligible_for_packet05_bootstrap"]

    posture = closeout["der02_posture_after_closeout"]
    assert posture["der02_status"] == "FUTURE_SOURCE_ONLY_NONMOVING_FOR_THIS_ATTEMPT_CYCLE"
    assert posture["der02_replay_allowed"] is False
    assert posture["der02_new_attempt_allowed_without_new_evidence"] is False
    assert posture["der02_execution_authorization"] == "NONE"
    assert posture["der02_attempt_cycle_closeout_complete"] is True

    decision = closeout["closeout_decision"]
    assert decision["terminal_outcome"] == "STAT_DER02_POST_ATTEMPT_NONMOVEMENT_CLOSEOUT_DER02_CLOSED"
    assert decision["authorized_attempt_consumed"] is True
    assert decision["remaining_der02_discharge_attempt_authorization"] == 0
    assert decision["blocker_movement"] == "UNCHANGED"
    assert decision["theorem_gap_delta_counted"] == 0
    assert decision["der02_future_source_only"] is True
    assert decision["der02_replay_allowed"] is False

    assert authorization["authorization_decision"]["one_bounded_der02_discharge_attempt_authorized"] is True
    assert execution["payload"]["post_attempt_state"]["further_der02_discharge_attempt_authorization"] == "NONE"

    validation = closeout["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_stat_der02_post_attempt_nonmovement_closeout_review_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert closeout["payload_sha256"] == _canonical_hash({k: v for k, v in closeout.items() if k != "payload_sha256"})