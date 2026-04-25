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
    / "post_recovery_stat_post_der_cycle_exhaustion_readout_review_20260424_v0.json"
)
DER01_CLOSEOUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der01_post_attempt_nonmovement_closeout_review_20260424_v0.json"
)
DER02_CLOSEOUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_post_attempt_nonmovement_closeout_review_20260424_v0.json"
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


def test_post_recovery_stat_post_der_cycle_exhaustion_readout_review_gate() -> None:
    report = _read_json(REPORT_PATH)
    der01_closeout = _read_json(DER01_CLOSEOUT_PATH)
    der02_closeout = _read_json(DER02_CLOSEOUT_PATH)
    evidence = _read_json(STAT_EVIDENCE_REPORT_PATH)
    qualification = _read_json(QUALIFICATION_REPORT_PATH)
    packet05 = _read_json(PACKET05_REPORT_PATH)

    assert report["schema_id"] == "POST_RECOVERY_STAT_POST_DER_CYCLE_EXHAUSTION_READOUT_REVIEW_20260424_v0"
    assert report["artifact_id"] == "post_recovery_stat_post_der_cycle_exhaustion_readout_review_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_STAT_POST_DER_CYCLE_EXHAUSTION_READOUT_REVIEW_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "DER01_AND_DER02_POST_ATTEMPT_NONMOVEMENT_CLOSEOUTS_AVAILABLE"
    assert trigger["der01_closeout_review"] == (
        "formal/output/reports/post_recovery_stat_der01_post_attempt_nonmovement_closeout_review_20260424_v0.json"
    )
    assert trigger["der02_closeout_review"] == (
        "formal/output/reports/post_recovery_stat_der02_post_attempt_nonmovement_closeout_review_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_POST_DER_CYCLE_EXHAUSTION_READOUT"
    assert boundary["records_readout_only"] is True
    assert boundary["review_executes_discharge"] is False
    assert boundary["review_counts_theorem_gap_delta"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["gr_work_allowed"] is False
    assert boundary["rl10_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    readout = report["exhaustion_readout"]
    assert readout["der01_attempt_cycle_closed_nonmoving"] is True
    assert readout["der02_attempt_cycle_closed_nonmoving"] is True
    assert readout["der01_terminal_outcome"] == der01_closeout["attempt_cycle_state"]["terminal_outcome"]
    assert readout["der02_terminal_outcome"] == der02_closeout["attempt_cycle_state"]["terminal_outcome"]
    assert readout["theorem_gap_delta"] == 0
    assert readout["theorem_gap_delta_counted"] == 0
    assert readout["fresh_movement_machine_pinned"] is False
    assert readout["der01_remaining_attempt_authorization"] == der01_closeout["attempt_cycle_state"][
        "remaining_der01_discharge_attempt_authorization"
    ]
    assert readout["der02_remaining_attempt_authorization"] == der02_closeout["attempt_cycle_state"][
        "remaining_der02_discharge_attempt_authorization"
    ]
    assert readout["any_remaining_der_attempt_authorization"] is False
    assert readout["stat_fresh_movement_terminal_outcome"] == evidence["summary"]["terminal_outcome"]
    assert readout["selected_row"] == qualification["summary"]["selected_row"]
    assert readout["packet05_eligible_for_bootstrap"] == packet05["summary"]["eligible_for_packet05_bootstrap"]

    hold = report["execution_hold_state"]
    assert hold["stat_execution_state"] == "HELD_POST_DER_ATTEMPT_EXHAUSTION"
    assert hold["replay_allowed_for_der01"] is False
    assert hold["replay_allowed_for_der02"] is False
    assert hold["der_execution_authorization_available_now"] == "NONE"
    assert hold["requires_new_source_evidence_or_new_declared_candidate"] is True

    reassess = report["non_replay_frontier_reassessment"]
    assert reassess["answer"] == "NO_NEW_FRONTIER_OPENED_BY_THIS_READOUT"
    assert reassess["outside_stat_frontier_authorized_now"] is False

    for disallowed in (
        "rerun_der01_attempt_without_new_authorization",
        "rerun_der02_attempt_without_new_authorization",
        "count_theorem_gap_delta_from_nonmoving_der_attempts",
        "open_packet05",
        "open_seam_work",
        "open_gr_work",
        "open_rl10_work",
        "invoke_master_action",
        "claim_promotion_or_closure",
    ):
        assert disallowed in report["disallowed_next_actions"]

    decision = report["readout_decision"]
    assert decision["terminal_outcome"] == "STAT_POST_DER_CYCLE_EXHAUSTION_RECORDED_EXECUTION_HELD"
    assert decision["der01_cycle_closed_nonmoving"] is True
    assert decision["der02_cycle_closed_nonmoving"] is True
    assert decision["any_remaining_der_attempt_authorization"] is False
    assert decision["theorem_gap_delta_counted"] == 0
    assert decision["fresh_movement_machine_pinned"] is False
    assert decision["stat_execution_held"] is True

    validation = report["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_stat_post_der_cycle_exhaustion_readout_review_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})