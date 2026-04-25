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
    / "post_recovery_non_stat_frontier_phase7_validation_readout_20260424_v0.json"
)
PHASE1_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase1_baseline_lock_20260424_v0.json"
)
PHASE2_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase2_candidate_intake_20260424_v0.json"
)
PHASE3_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase3_strict_admissibility_filter_20260424_v0.json"
)
PHASE4_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase4_decision_packet_20260424_v0.json"
)
PHASE5_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase5_fallback_hold_design_packet_20260424_v0.json"
)
PHASE6_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_non_stat_frontier_phase6_boundary_consolidation_20260424_v0.json"
)
NON_REPLAY_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_non_replay_frontier_reassessment_20260424_v0.json"
)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_non_stat_frontier_phase7_validation_readout_gate() -> None:
    report = _read_json(REPORT_PATH)
    phase1 = _read_json(PHASE1_PATH)
    phase2 = _read_json(PHASE2_PATH)
    phase3 = _read_json(PHASE3_PATH)
    phase4 = _read_json(PHASE4_PATH)
    phase5 = _read_json(PHASE5_PATH)
    phase6 = _read_json(PHASE6_PATH)
    non_replay = _read_json(NON_REPLAY_PATH)

    assert report["schema_id"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE7_VALIDATION_READOUT_20260424_v0"
    assert report["artifact_id"] == "post_recovery_non_stat_frontier_phase7_validation_readout_20260424_v0"
    assert report["status"] == "DECLARATION_ONLY_NON_STAT_FRONTIER_PHASE7_VALIDATION_READOUT_NONCLAIM"

    trigger = report["trigger"]
    assert trigger["source"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE6_BOUNDARY_CONSOLIDATION"
    assert trigger["source_report"] == (
        "formal/output/reports/post_recovery_non_stat_frontier_phase6_boundary_consolidation_20260424_v0.json"
    )

    boundary = report["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_PHASE7_VALIDATION_READOUT"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["validation_readout_only"] is True
    assert boundary["review_counts_theorem_gap_delta"] is False
    assert boundary["packet05_bootstrap_allowed"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["gr_work_allowed"] is False
    assert boundary["rl10_work_allowed"] is False
    assert boundary["master_action_allowed"] is False
    assert boundary["promotion_or_closure_language_allowed"] is False

    assert phase1["decision"]["phase1_baseline_lock_complete"] is True
    assert phase2["intake_decision"]["phase2_candidate_intake_complete"] is True
    assert phase3["decision"]["phase3_strict_filter_complete"] is True
    assert phase4["frontier_decision"]["terminal_outcome"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"
    assert phase5["decision"]["phase5_fallback_hold_design_complete"] is True
    assert phase6["decision"]["phase6_consolidation_complete"] is True

    readout = report["phase_validation_readout"]
    assert len(readout["focused_gate_results"]) == 6
    assert readout["focused_gate_pass_count"] == 6
    assert readout["focused_gate_fail_count"] == 0
    for row in readout["focused_gate_results"]:
        assert row["result"] == "PASS"
    assert readout["compatibility_bundle_result"] == "PASS_8"
    assert readout["compatibility_bundle_fail_count"] == 0

    posture = report["posture_readout"]
    assert posture["execution_authorization_changed"] is False
    assert posture["execution_authorization"] == "NONE"
    assert posture["selected_lane_emerged"] is False
    assert posture["selected_lane"] == "NONE"
    assert posture["cosmo_sr_fresh_hypothesis_authorized"] is False
    assert posture["final_posture"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"

    assert phase4["frontier_decision"]["execution_authorization"] == "NONE"
    assert phase4["frontier_decision"]["selected_lane"] == "NONE"
    assert phase5["decision"]["execution_authorization"] == "NONE"
    assert phase5["decision"]["selected_lane"] == "NONE"
    assert phase5["decision"]["cosmo_sr_fresh_hypothesis_authorized"] is False
    assert non_replay["decision"]["execution_held"] is True

    phase8 = report["phase8_readiness"]
    assert phase8["phase8_staging_readout_authorized"] is True
    assert phase8["required_phase7_preconditions_met"] is True
    assert phase8["next_action"] == "EXECUTE_PHASE8_STAGING_AND_FINAL_READOUT"

    decision = report["decision"]
    assert decision["terminal_outcome"] == "POST_RECOVERY_NON_STAT_FRONTIER_PHASE7_VALIDATION_READOUT_COMPLETE"
    assert decision["phase7_validation_complete"] is True
    assert decision["all_focused_gates_passed"] is True
    assert decision["compatibility_bundle_passed"] is True
    assert decision["final_posture"] == "HOLD_NO_ADMISSIBLE_NON_STAT_FRONTIER"
    assert decision["phase8_staging_readout_authorized"] is True

    for disallowed in (
        "author_cosmo_sr_fresh_hypothesis_design_packet_under_current_hold",
        "authorize_cosmo_sr_hypothesis_execution",
        "select_lane_without_new_admissible_filter_pass",
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
    assert "test_post_recovery_non_stat_frontier_phase7_validation_readout_gate.py" in validation[
        "targeted_gate_command"
    ]

    assert report["payload_sha256"] == _canonical_hash({k: v for k, v in report.items() if k != "payload_sha256"})
